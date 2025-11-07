/* Enhanced_OCED_Constraints.als */
open util/ordering[Time]

sig Time {}

abstract sig ObjectType {}
one sig Case, Activity, Resource, Incident extends ObjectType {}

abstract sig EventType {}
one sig Start, Complete, Assign, Escalate, Resolve extends EventType {}

sig Object {
    type: ObjectType,
    created: Time,
    deleted: lone Time
} {
    // Objects cannot be deleted before creation
    no deleted or deleted in created.nexts
}

sig Event {
    type: EventType,
    timestamp: Time
}

sig Observe {
    event: one Event,
    object: one Object,
    relation: EventType
} {
    // Events cannot reference deleted objects
    object.deleted not in event.timestamp
    event.timestamp in object.created.nexts
}

// Enhanced Constraints
fact NoOrphanedObjects {
    all o: Object | some obs: Observe | obs.object = o
}

fact NoOrphanedEvents {
    all e: Event | some obs: Observe | obs.event = e
}

fact ConsistentTemporalOrdering {
    // Events for same object must be temporally ordered
    all o: Object | all disj e1, e2: Event | 
        (some obs1, obs2: Observe | obs1.object = o and obs1.event = e1 and 
                                  obs2.object = o and obs2.event = e2) 
        implies (e1.timestamp != e2.timestamp)
}

fact MaximumObservesConstraint {
    all e: Event | #{o: Object | some obs: Observe | obs.event = e and obs.object = o} <= 10
}

fact IncidentLifecycleConstraints {
    all i: Object | i.type = Incident implies {
        // Every incident must have a start event
        some start_evt: Event, obs: Observe | 
            obs.object = i and obs.event = start_evt and start_evt.type = Start
        
        // Every incident must eventually be resolved or deleted
        some resolve_evt: Event, obs: Observe | 
            obs.object = i and obs.event = resolve_evt and 
            (resolve_evt.type = Resolve or i.deleted != none)
    }
}

// Assertions for verification
assert NoTemporalAnomalies {
    no o: Object | some e: Event | 
        (some obs: Observe | obs.object = o and obs.event = e) and
        e.timestamp in o.created.prevs
}

assert AllObjectsParticipate {
    all o: Object | some e: Event, obs: Observe | obs.object = o and obs.event = e
}

assert MaximumCardinalityRespected {
    all e: Event | #{obs: Observe | obs.event = e} <= 10
}

check NoTemporalAnomalies for 10
check AllObjectsParticipate for 10  
check MaximumCardinalityRespected for 10

pred showValidInstance {
    #Object >= 5
    #Event >= 8
    #Observe >= 12
    all o: Object | some e: Event | e.timestamp = o.created
}

run showValidInstance for 8 but 15 Time
