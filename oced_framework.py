# oced_framework.py
import xml.etree.ElementTree as ET
from datetime import datetime
from typing import Dict, List, Set, Any, Optional
from dataclasses import dataclass
from enum import Enum
import subprocess
import json
import logging

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

class ObjectType(Enum):
    CASE = "case"
    ACTIVITY = "activity"
    RESOURCE = "resource"
    INCIDENT = "incident"

class EventType(Enum):
    START = "start"
    COMPLETE = "complete"
    ASSIGN = "assign"
    ESCALATE = "escalate"
    RESOLVE = "resolve"

class RelationType(Enum):
    HAS_EVENT = "has_event"
    INVOLVES = "involves"
    FOLLOWS = "follows"
    ASSIGNED_TO = "assigned_to"

@dataclass
class Object:
    id: str
    type: ObjectType
    attributes: Dict[str, Any]
    created: datetime
    deleted: Optional[datetime] = None

@dataclass
class Event:
    id: str
    type: EventType
    timestamp: datetime
    attributes: Dict[str, Any]
    linked_objects: Set[str]  # Object IDs

@dataclass
class Observe:
    event_id: str
    object_id: str
    relation: RelationType

class OCEDMetaModel:
    def __init__(self, max_observes: int = 10):
        self.objects: Dict[str, Object] = {}
        self.events: Dict[str, Event] = {}
        self.observes: List[Observe] = []
        self.max_observes = max_observes
        self._constraints_violated = []
    
    def add_object(self, obj_id: str, obj_type: ObjectType, 
                  attributes: Dict[str, Any], created: datetime) -> bool:
        """Add object with validation"""
        if obj_id in self.objects:
            self._constraints_violated.append(f"Duplicate object ID: {obj_id}")
            return False
            
        obj = Object(obj_id, obj_type, attributes, created)
        self.objects[obj_id] = obj
        return True
    
    def add_event(self, event_id: str, event_type: EventType, 
                  timestamp: datetime, attributes: Dict[str, Any],
                  linked_objects: List[str]) -> bool:
        """Add event with validation"""
        if event_id in self.events:
            self._constraints_violated.append(f"Duplicate event ID: {event_id}")
            return False
        
        # Validate linked objects exist
        for obj_id in linked_objects:
            if obj_id not in self.objects:
                self._constraints_violated.append(f"Unknown object ID: {obj_id}")
                return False
        
        # Check max observes constraint
        if len(linked_objects) > self.max_observes:
            self._constraints_violated.append(
                f"Event {event_id} exceeds max observes: {len(linked_objects)} > {self.max_observes}"
            )
            return False
        
        event = Event(event_id, event_type, timestamp, attributes, set(linked_objects))
        self.events[event_id] = event
        
        # Create observe relations
        for obj_id in linked_objects:
            observe = Observe(event_id, obj_id, RelationType.INVOLVES)
            self.observes.append(observe)
        
        return True
    
    def validate_temporal_consistency(self) -> bool:
        """Validate temporal constraints"""
        violations = []
        
        for event in self.events.values():
            for obj_id in event.linked_objects:
                obj = self.objects[obj_id]
                # Event cannot occur before object creation
                if event.timestamp < obj.created:
                    violations.append(
                        f"Event {event.id} timestamp {event.timestamp} "
                        f"before object {obj_id} creation {obj.created}"
                    )
                
                # Event cannot occur after object deletion
                if obj.deleted and event.timestamp > obj.deleted:
                    violations.append(
                        f"Event {event.id} timestamp {event.timestamp} "
                        f"after object {obj_id} deletion {obj.deleted}"
                    )
        
        self._constraints_violated.extend(violations)
        return len(violations) == 0
    
    def to_alloy_format(self) -> str:
        """Convert OCED model to Alloy format for verification"""
        alloy_template = """
        module OCED_Instance

        open util/ordering[Time]

        sig Time {{}}

        {}

        {}

        {}

        fact TemporalConstraints {{
            {}
        }}

        run {{}} for exactly {} Time, exactly {} Object, exactly {} Event
        """
        
        # Generate object signatures
        objects_sig = "\n".join([
            f"one sig Obj_{obj.id} extends Object {{}}"
            for obj in self.objects.values()
        ])
        
        # Generate event signatures  
        events_sig = "\n".join([
            f"one sig Evt_{event.id} extends Event {{}}"
            for event in self.events.values()
        ])
        
        # Generate observe facts
        observes_facts = "\n".join([
            f"fact {{ some obs: Observe | obs.event = Evt_{obs.event_id} and obs.object = Obj_{obs.object_id} }}"
            for obs in self.observes
        ])
        
        # Generate temporal constraints
        temporal_constraints = "\n".join([
            f"Evt_{event.id}.timestamp in Obj_{obj_id}.created.nexts"
            for event in self.events.values()
            for obj_id in event.linked_objects
        ])
        
        return alloy_template.format(
            objects_sig, events_sig, observes_facts, temporal_constraints,
            len(set(ev.timestamp for ev in self.events.values())),
            len(self.objects), len(self.events)
        )
    
    def verify_with_alloy(self) -> bool:
        """Perform formal verification using Alloy Analyzer"""
        alloy_code = self.to_alloy_format()
        
        # Write Alloy code to temporary file
        with open("temp_instance.als", "w") as f:
            f.write(alloy_code)
        
        try:
            # Run Alloy Analyzer (requires Alloy to be installed)
            result = subprocess.run(
                ["java", "-jar", "alloy.jar", "temp_instance.als"],
                capture_output=True, text=True, timeout=30
            )
            
            if "No counterexample found" in result.stdout:
                logger.info("✓ Formal verification passed")
                return True
            else:
                logger.error("✗ Formal verification failed")
                logger.error(result.stdout)
                return False
                
        except Exception as e:
            logger.error(f"Alloy verification failed: {e}")
            return False
    
    def get_violations(self) -> List[str]:
        return self._constraints_violated

class XESParser:
    """Parser for XES event logs"""
    
    def __init__(self):
        self.namespaces = {'xes': 'http://www.xes-standard.org/'}
    
    def parse(self, file_path: str) -> OCEDMetaModel:
        """Parse XES file into OCED model"""
        tree = ET.parse(file_path)
        root = tree.getroot()
        
        oced_model = OCEDMetaModel()
        
        # Extract traces (cases)
        for trace in root.findall('.//xes:trace', self.namespaces):
            case_id = self._get_attribute(trace, 'concept:name')
            if not case_id:
                continue
                
            # Create case object
            oced_model.add_object(
                f"case_{case_id}", ObjectType.CASE, 
                {'name': case_id}, datetime.now()
            )
            
            # Extract events
            for event in trace.findall('.//xes:event', self.namespaces):
                event_id = self._get_attribute(event, 'concept:name')
                timestamp_str = self._get_attribute(event, 'time:timestamp')
                
                if event_id and timestamp_str:
                    timestamp = datetime.fromisoformat(
                        timestamp_str.replace('Z', '+00:00')
                    )
                    
                    # Create event
                    attributes = self._extract_attributes(event)
                    oced_model.add_event(
                        f"event_{event_id}", EventType.START,
                        timestamp, attributes, [f"case_{case_id}"]
                    )
        
        return oced_model
    
    def _get_attribute(self, element, key: str) -> Optional[str]:
        attr = element.find(f".//xes:string[@key='{key}']", self.namespaces)
        return attr.get('value') if attr is not None else None
    
    def _extract_attributes(self, event_element) -> Dict[str, Any]:
        attributes = {}
        for attr in event_element.findall('.//xes:*', self.namespaces):
            if 'key' in attr.attrib and 'value' in attr.attrib:
                attributes[attr.attrib['key']] = attr.attrib['value']
        return attributes

class Neo4jExporter:
    """Export OCED model to Neo4j"""
    
    def __init__(self, uri: str, user: str, password: str):
        from neo4j import GraphDatabase
        self.driver = GraphDatabase.driver(uri, auth=(user, password))
    
    def export_oced_model(self, oced_model: OCEDMetaModel):
        """Export OCED model to Neo4j graph database"""
        
        def create_nodes_and_relationships(tx):
            # Create object nodes
            for obj in oced_model.objects.values():
                tx.run(
                    "CREATE (o:Object {id: $id, type: $type, attributes: $attributes, created: $created})",
                    id=obj.id, type=obj.type.value, attributes=obj.attributes, 
                    created=obj.created.isoformat()
                )
            
            # Create event nodes
            for event in oced_model.events.values():
                tx.run(
                    "CREATE (e:Event {id: $id, type: $type, timestamp: $timestamp, attributes: $attributes})",
                    id=event.id, type=event.type.value, 
                    timestamp=event.timestamp.isoformat(), attributes=event.attributes
                )
                
                # Create relationships
                for obj_id in event.linked_objects:
                    tx.run(
                        "MATCH (e:Event {id: $event_id}), (o:Object {id: $object_id}) "
                        "CREATE (e)-[:INVOLVES]->(o)",
                        event_id=event.id, object_id=obj_id
                    )
        
        with self.driver.session() as session:
            session.write_transaction(create_nodes_and_relationships)
    
    def execute_cypher_query(self, query: str) -> List[Dict]:
        """Execute Cypher query and return results"""
        with self.driver.session() as session:
            result = session.run(query)
            return [dict(record) for record in result]
    
    def close(self):
        self.driver.close()

# Enhanced Analysis Queries
class OCEDAnalyzer:
    def __init__(self, neo4j_exporter: Neo4jExporter):
        self.neo4j = neo4j_exporter
    
    def activity_frequency_analysis(self):
        """Analyze activity frequency"""
        query = """
        MATCH (e:Event)
        RETURN e.type as activity_type, count(*) as frequency
        ORDER BY frequency DESC
        """
        return self.neo4j.execute_cypher_query(query)
    
    def object_interaction_analysis(self):
        """Analyze object interactions"""
        query = """
        MATCH (o1:Object)-[:INVOLVES]-(e:Event)-[:INVOLVES]-(o2:Object)
        WHERE o1.id <> o2.id
        RETURN o1.id as object1, o2.id as object2, count(*) as interaction_count
        ORDER BY interaction_count DESC
        """
        return self.neo4j.execute_cypher_query(query)
    
    def temporal_pattern_analysis(self):
        """Analyze temporal patterns"""
        query = """
        MATCH (e:Event)
        WITH e.type as activity, e.timestamp as timestamp
        ORDER BY timestamp
        WITH activity, collect(timestamp) as timestamps
        RETURN activity, 
               timestamps[0] as first_occurrence,
               timestamps[size(timestamps)-1] as last_occurrence,
               size(timestamps) as total_occurrences
        """
        return self.neo4j.execute_cypher_query(query)
    
    def process_variant_analysis(self):
        """Identify process variants"""
        query = """
        MATCH path = (o:Object)-[:INVOLVES]-(e:Event)
        WITH o.id as case_id, collect(e.type) as event_sequence
        RETURN event_sequence, count(*) as variant_frequency
        ORDER BY variant_frequency DESC
        """
        return self.neo4j.execute_cypher_query(query)

# Improved Implementation with Enhanced Features
class EnhancedOCEDFramework:
    def __init__(self, xes_file_path: str, neo4j_uri: str, 
                 neo4j_user: str, neo4j_password: str):
        self.xes_parser = XESParser()
        self.neo4j_exporter = Neo4jExporter(neo4j_uri, neo4j_user, neo4j_password)
        self.analyzer = OCEDAnalyzer(self.neo4j_exporter)
        self.xes_file_path = xes_file_path
    
    def run_complete_analysis(self):
        """Run complete OCED analysis pipeline"""
        logger.info("Step 1: Parsing XES file...")
        oced_model = self.xes_parser.parse(self.xes_file_path)
        
        logger.info("Step 2: Validating temporal consistency...")
        if not oced_model.validate_temporal_consistency():
            logger.warning("Temporal consistency violations found:")
            for violation in oced_model.get_violations():
                logger.warning(f"  - {violation}")
        
        logger.info("Step 3: Performing formal verification...")
        verification_passed = oced_model.verify_with_alloy()
        
        if verification_passed:
            logger.info("Step 4: Exporting to Neo4j...")
            self.neo4j_exporter.export_oced_model(oced_model)
            
            logger.info("Step 5: Running analytical queries...")
            results = self._run_analytical_queries()
            
            logger.info("Step 6: Generating insights...")
            insights = self._generate_insights(results)
            
            return {
                'verification_passed': verification_passed,
                'violations': oced_model.get_violations(),
                'analytical_results': results,
                'insights': insights
            }
        else:
            return {
                'verification_passed': False,
                'violations': oced_model.get_violations(),
                'error': 'Formal verification failed'
            }
    
    def _run_analytical_queries(self):
        """Execute all analytical queries"""
        return {
            'activity_frequency': self.analyzer.activity_frequency_analysis(),
            'object_interactions': self.analyzer.object_interaction_analysis(),
            'temporal_patterns': self.analyzer.temporal_pattern_analysis(),
            'process_variants': self.analyzer.process_variant_analysis()
        }
    
    def _generate_insights(self, results):
        """Generate business insights from analytical results"""
        insights = []
        
        # Activity frequency insights
        activity_freq = results['activity_frequency']
        if activity_freq:
            most_frequent = activity_freq[0]['activity_type']
            least_frequent = activity_freq[-1]['activity_type']
            insights.append(f"Most frequent activity: {most_frequent}")
            insights.append(f"Least frequent activity: {least_frequent}")
        
        # Process variant insights
        variants = results['process_variants']
        if variants:
            total_variants = len(variants)
            dominant_variant_freq = variants[0]['variant_frequency'] if variants else 0
            insights.append(f"Total process variants: {total_variants}")
            insights.append(f"Dominant variant frequency: {dominant_variant_freq}")
        
        return insights

# Usage Example
if __name__ == "__main__":
    # Initialize the enhanced framework
    framework = EnhancedOCEDFramework(
        xes_file_path="bpi2013.xes",  # Replace with your XES file
        neo4j_uri="bolt://localhost:7687",
        neo4j_user="neo4j",
        neo4j_password="password"
    )
    
    # Run complete analysis
    results = framework.run_complete_analysis()
    
    # Print results
    print("\n" + "="*50)
    print("OCED FRAMEWORK ANALYSIS RESULTS")
    print("="*50)
    
    print(f"Formal Verification: {'PASSED' if results['verification_passed'] else 'FAILED'}")
    
    if results['violations']:
        print(f"\nConstraint Violations ({len(results['violations'])}):")
        for violation in results['violations']:
            print(f"  - {violation}")
    
    if results.get('insights'):
        print(f"\nBusiness Insights:")
        for insight in results['insights']:
            print(f"  • {insight}")
    
    # Close Neo4j connection
    framework.neo4j_exporter.close()