open util/ordering[Time]

abstract sig EventType {}
abstract sig ObjectType {}
abstract sig RelationType {}
abstract sig AttrName {}
abstract sig AttrValue {}

sig Time {}

sig Attr {
  name: AttrName,
  value: AttrValue
}

sig Object {
  otype: ObjectType,
  attrs: set Attr
}

sig Event {
  etype: EventType,
  time: Time,
  attrs: set Attr
}

sig Observe {
  event: Event,
  object: Object
}

sig Relation {
  from: Object,
  to: Object,
  relType: RelationType
}

fact ValidAttrs {
  all o: Object | all a: o.attrs | a.name in AttrName and a.value in AttrValue
  all e: Event  | all a: e.attrs | a.name in AttrName and a.value in AttrValue
}

let MaxObserves = 3

fact MaxObserveLimit {
  all e: Event | 
    let objs = { o: Object | some obs: Observe | obs.event = e and obs.object = o } |
      #objs <= MaxObserves
}

run {} for
  5 Object, 5 Event, 10 Attr, 5 AttrName, 5 AttrValue, 3 Relation, 3 RelationType, 3 EventType, 3 ObjectType, 5 Time, 10 Observe
