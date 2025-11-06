/* OCED_MetaModel.als */
open util/ordering[Time]

sig Time {}

sig ObjectType {}
sig EventType {}
sig RelationType {}
sig AttributeName {}

abstract sig Value {}
sig IntValue extends Value { value: Int }
sig StringValue extends Value { value: String }
sig TimestampValue extends Value { value: Time }

sig Object {
    type: ObjectType,
    attributes: AttributeName -> lone Value,
    created: Time,
    deleted: lone Time
}

sig Event {
    type: EventType,
    timestamp: Time,
    attributes: AttributeName -> lone Value
}

sig Observe {
    event: Event,
    object: Object,
    relation: RelationType
}

fact TemporalConsistency {
    // Objects cannot be deleted before creation
    all o: Object | o.deleted in Time implies o.deleted in o.created.nexts
    
    // Events cannot reference deleted objects
    all obs: Observe | obs.object.deleted not in Event.timestamp
    all obs: Observe | obs.event.timestamp in obs.object.created.nexts
}

fact AttributeConstraints {
    // Attribute values must be valid for their type
    all o: Object | all attr: o.attributes.Value | 
        attr in IntValue or attr in StringValue or attr in TimestampValue
}

fact ObjectLifetime {
    // Objects exist from creation to deletion (or forever if not deleted)
    all o: Object | no o.deleted implies o.created = first
}

// Configuration parameters
let MaxObserves = 10
let MaxTime = 10

assert MaxObserveProperty {
    all e: Event | 
        let objs = { o: Object | some obs: Observe | obs.event = e and obs.object = o } | 
        #objs <= MaxObserves
}

check MaxObserveProperty for 5 but exactly 10 Time

pred show() {
    #Object >= 3
    #Event >= 5
    #Observe >= 8
}

run show for 5 but 10 Time