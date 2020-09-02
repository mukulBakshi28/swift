// RUN: %target-run-simple-swift

// REQUIRES: executable_test

//===----------------------------------------------------------------------===//
// Use of protocols with Self or associated type requirements
//===----------------------------------------------------------------------===//

protocol P {
  associatedtype Q
  func returnSelf() -> Self
  func takesNestedSelf(arg: (Self) -> ())
  func printANumber()
}

struct S: P {
  typealias Q = Int

  func returnSelf() -> Self { self }
  func takesNestedSelf(arg: (Self) -> ()) { arg(self) }
  func printANumber() { print("123") }
}

let p: P = S()

// CHECK: 123
p.returnSelf().printANumber()

// CHECK: 123
p.takesNestedSelf { $0.printANumber() }

// CHECK: 123
p.printANumber()

func takesP(arg: P) {
  // CHECK: 123
  p.returnSelf().printANumber()

  // CHECK: 123
  p.takesNestedSelf { $0.printANumber() }

  // CHECK: 123
  p.printANumber()
}

takesP(arg: p)

// CHECK: true
print(S() is P)

// CHECK: true
print(p is P)

// CHECK: 123
(S() as P).printANumber()
