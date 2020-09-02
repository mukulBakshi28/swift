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
