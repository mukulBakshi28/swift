// RUN: %target-typecheck-verify-swift

//===----------------------------------------------------------------------===//
// Use of protocols with Self or associated type requirements
//===----------------------------------------------------------------------===//

protocol P1 {
  associatedtype Q
  func returnSelf() -> Self
  func returnAssoc() -> Q
}

struct S1: P1 {
  typealias Q = Int
  func returnSelf() -> Self { self }
  func returnAssoc() -> Q { 0 }
}

let p1: P1 = S1()
_ = p1.returnSelf() // ok
_ = p1.returnAssoc() // expected-error {{member 'returnAssoc' cannot be used on value of protocol type 'P1'; use a generic constraint instead}}

func takesP1(arg: P1) {
  _ = arg.returnSelf() // ok
  _ = p1.returnAssoc() // expected-error {{member 'returnAssoc' cannot be used on value of protocol type 'P1'; use a generic constraint instead}}
}

takesP1(arg: p1) // ok

let p1Array: [P1] = [S1()] // ok
p1Array.forEach { 
  _ = $0.returnSelf() // ok
  _ = $0.returnAssoc() // expected-error {{member 'returnAssoc' cannot be used on value of protocol type 'P1'; use a generic constraint instead}}
}

protocol P2 {
  associatedtype Q
  func takesSelf(_: Self)
  func takesAssoc(_: Q)
  func takesNestedSelf(closure: (Self) -> ())
  func takesNestedAssoc(closure: (Q) -> ())
}

struct S2: P2 {
  typealias Q = Int
  func takesSelf(_: Self) {}
  func takesAssoc(_: Q) {}
  func takesNestedSelf(closure: (Self) -> ()) { print(closure(S2())) }
  func takesNestedAssoc(closure: (Q) -> ()) { print(closure(0)) }
}

let p2: P2 = S2()
p2.takesSelf(S2()) // expected-error {{member 'takesSelf' cannot be used on value of protocol type 'P2'; use a generic constraint instead}}

// FIXME: Silence argument mismatches on unsupported accesses?
p2.takesAssoc(0)
// expected-error@-1 {{member 'takesAssoc' cannot be used on value of protocol type 'P2'; use a generic constraint instead}} 
// expected-error@-2 {{cannot convert value of type 'Int' to expected argument type 'P2.Q'}}
p2.takesNestedSelf { _ in } // okay
p2.takesNestedAssoc { _ in } 
// expected-error@-1 {{member 'takesNestedAssoc' cannot be used on value of protocol type 'P2'; use a generic constraint instead}}
// expected-error@-2 {{cannot convert value of type '(_) -> ()' to expected argument type '(P2.Q) -> ()'}}

func takesP2(arg: P2) {
  arg.takesSelf(S2()) // expected-error {{member 'takesSelf' cannot be used on value of protocol type 'P2'; use a generic constraint instead}}
  arg.takesAssoc(0) 
  // expected-error@-1 {{member 'takesAssoc' cannot be used on value of protocol type 'P2'; use a generic constraint instead}} 
  // expected-error@-2 {{cannot convert value of type 'Int' to expected argument type 'P2.Q'}}
  arg.takesNestedSelf { _ in } // okay
  arg.takesNestedAssoc { _ in } 
  // expected-error@-1 {{member 'takesNestedAssoc' cannot be used on value of protocol type 'P2'; use a generic constraint instead}}
  // expected-error@-2 {{cannot convert value of type '(_) -> ()' to expected argument type '(P2.Q) -> ()'}}
}

takesP2(arg: p2) // okay

protocol P3 {
  associatedtype Q
  var assocProp: Q { get }
  subscript(q: Q) -> Q { get }
  var selfProp: Self { get }
}

struct S3: P3 {
  typealias Q = Int
  var assocProp: Q { 0 }
  subscript(q: Q) -> Q { 0 }
  var selfProp: Self { self }
}

let p3: P3 = S3()
_ = p3.assocProp // expected-error {{member 'assocProp' cannot be used on value of protocol type 'P3'; use a generic constraint instead}}
_ = p3[0]
// expected-error@-1 {{member 'subscript' cannot be used on value of protocol type 'P3'; use a generic constraint instead}}
// expected-error@-2 {{cannot convert value of type 'Int' to expected argument type 'P3.Q'}}
_ = p3.selfProp

func takesP3(arg: P3) {
  _ = arg.assocProp // expected-error {{member 'assocProp' cannot be used on value of protocol type 'P3'; use a generic constraint instead}}
  _ = arg[0]
  // expected-error@-1 {{member 'subscript' cannot be used on value of protocol type 'P3'; use a generic constraint instead}}
  // expected-error@-2 {{cannot convert value of type 'Int' to expected argument type 'P3.Q'}}
  _ = arg.selfProp
}

takesP3(arg: p3) // okay

protocol P4 {
  func foo(_: () -> Self)
  func bar(_: (inout Self) -> ())
}

struct S4: P4 {
  func foo(_: () -> Self) {}
  func bar(_: (inout Self) -> ()) {}
}

let p4: P4 = S4()
p4.foo { return S4() } // expected-error {{member 'foo' cannot be used on value of protocol type 'P4'; use a generic constraint instead}}
p4.bar { _ in } // expected-error {{member 'bar' cannot be used on value of protocol type 'P4'; use a generic constraint instead}}

func takesP4(arg: P4) {
  arg.foo { return S4() } // expected-error {{member 'foo' cannot be used on value of protocol type 'P4'; use a generic constraint instead}}
  arg.bar { _ in } // expected-error {{member 'bar' cannot be used on value of protocol type 'P4'; use a generic constraint instead}} 
}

_ = p1 as P1 // okay
_ = p2 as P2 // okay
_ = p3 as P3 // okay
_ = p4 as P4 // okay



// Whether a protocol member can be used with a given existential base type
// depends on how its interface type is spelled within the context of the base.

class Class {}
struct Struct<T> {}

protocol P5a where B == Struct<A> {
  associatedtype A
  associatedtype B
  associatedtype C

  var propA: A { get }
  var propB: Struct<B> { get }

  func takesA1(_: A)
  func takesB(_: B)
  func takesSelf(_: A, _: Self)
  func returnsC() -> C
}
protocol P5b: Class, P5a where A == Bool, C == Self {
  func takesA2(_: A)
}

func takesP5a(arg: P5a, never: Never) {
  // Self reference in invariant position.
  arg.takesB(never) // (Struct<Self.A>) -> ()
  // expected-error@-1 {{member 'takesB' cannot be used on value of protocol type 'P5a'; use a generic constraint instead}}
  // expected-error@-2 {{cannot convert value of type 'Never' to expected argument type 'Struct<P5a.A>'}}
}

func takesP5b(arg: P5b, never: Never) {
  // OK, A is known to be Bool on P5b.
  _ = arg.propA // Bool
  // OK, B is known to be Struct<Bool> on P5b.
  _ = arg.propB // Struct<Struct<Bool>>

  // OK, A is known to be Bool on P5b.
  arg.takesA1(true) // (Bool) -> ()
  arg.takesA2(true) // (Bool) -> ()

  // OK, B is known to be Struct<Bool> on P5b.
  arg.takesB(Struct<Bool>()) // (Struct<Bool>) -> ()

  // OK, D is in covariant position and known to be Self on P5b.
  let x1 /*: P5b*/ = arg.returnsC() // () -> Self
  let x2: P5a = arg.returnsC()
  let x3 = arg.returnsC()
  let x4: Class = arg.returnsC()

  // Self in contravariant position.
  arg.takesSelf(true, never) // (Bool, Self) -> ()
  // expected-error@-1 {{member 'takesSelf' cannot be used on value of protocol type 'P5b'; use a generic constraint instead}}
  // expected-error@-2 {{cannot convert value of type 'Never' to expected argument type 'Class'}}
}

protocol P6a where A == Bool {
  associatedtype A
}
protocol P6b {
  associatedtype A

  func takesA(arg: A) -> Self
}
func takesP6Composition(arg: P6a & P6b) -> P6a {
  // OK, A is known to be Bool on P6a & P6b.
  return arg.takesA(arg: true) // (Bool) -> P6a & P6b
}

class Class7: P7a {
  typealias A = Bool
}
protocol P7a {
  associatedtype A
}
protocol P7b: P7a {
  associatedtype B

  func takesA(arg: A)
}
func takesP7Composition(arg: P7b & Class7) {
  // OK, A is known to be Bool on P7b & Class7.
  arg.takesA(arg: true) // (Bool) -> ()
}

// FIXME: Check composition requirement signatures.
protocol P8a where A == Bool {
  associatedtype A
  func takesA(_: A)
}
protocol P8b where A == Never {
  associatedtype A
}
func takesP8Composition(arg: P8a & P8b) {
  arg.takesA(true)
}

// FIXME: Check composition requirement signatures.
protocol P9a {
  associatedtype A: Sequence
  func takesA(_: A)
}
protocol P9b where A == Bool {
  associatedtype A
}
func takesP9Composition(arg: P9a & P9b) {
  arg.takesA(true)
}
