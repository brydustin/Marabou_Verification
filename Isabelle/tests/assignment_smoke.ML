(* Run from the project root after: isabelle build -e -D Isabelle
   poly --script Isabelle/tests/assignment_smoke.ML
   These exercise the exported SML API, not the Isabelle proof kernel. *)
use "Isabelle/generated/Marabou_Assignment_Checker.ML";

structure A = Marabou_Assignment_Checker;
fun nat n = if n < 0 then raise Fail "negative index" else A.nat_of_integer n;
fun rat n d = if d = 0 then raise Fail "zero denominator"
  else A.fract (A.int_of_integer n) (A.int_of_integer d);
fun integer n = rat n 1;
fun expect label wanted actual =
  if wanted = actual then () else raise Fail ("failed: " ^ label);
fun point pairs = map (fn (x, q) => (nat x, q)) pairs;

(* x + y = 2, -1 <= x <= 1, y = ReLU(x). *)
val x = nat 0;
val y = nat 1;
val satQuery = A.make
  [A.RatEq (A.RatExpr (integer 0, [(integer 1, x), (integer 1, y)]), integer 2)]
  [A.RatLower (x, integer (~1)), A.RatUpper (x, integer 1)] [A.ReLU (x, y)];
val _ = expect "exact model" true
  (A.check_rat_assignment satQuery (point [(0, integer 1), (1, integer 1)]));
val _ = expect "extra variables are irrelevant" true
  (A.check_rat_assignment satQuery (point [(1, integer 1), (7, integer (~3)), (0, integer 1)]));
val _ = expect "duplicate variable" false
  (A.check_rat_assignment satQuery (point [(0, integer 1), (1, integer 1), (0, integer 5)]));
val _ = expect "unlisted variable is zero" false
  (A.check_rat_assignment satQuery (point [(0, integer 1)]));
val _ = expect "approximate value" false
  (A.check_rat_assignment satQuery
    (point [(0, integer 1), (1, rat 100000000000000000001 100000000000000000000)]));
val _ = expect "bound violation" false
  (A.check_rat_assignment satQuery (point [(0, rat 3 2), (1, rat 1 2)]));
val _ = expect "ReLU violation with linear atoms satisfied" false
  (A.check_rat_assignment satQuery (point [(0, rat (~1) 2), (1, rat 5 2)]));
val inactiveQuery = A.make
  [A.RatLe (A.RatExpr (integer 0, [(integer 1, x), (integer 1, y)]), integer 0)]
  [A.RatLower (x, integer (~1)), A.RatUpper (y, integer 1)] [A.ReLU (x, y)];
val _ = expect "inactive phase model" true
  (A.check_rat_assignment inactiveQuery (point [(0, rat (~1) 2), (1, integer 0)]));
val _ = expect "inactive phase with positive output" false
  (A.check_rat_assignment inactiveQuery (point [(0, rat (~1) 2), (1, rat 1 2)]));
val geQuery = A.make
  [A.RatGe (A.RatExpr (rat 1 4, [(integer 2, x)]), integer 1)] [] [];
val _ = expect "greater-or-equal atom at equality" true
  (A.check_rat_assignment geQuery (point [(0, rat 3 8)]));
val _ = expect "greater-or-equal atom just below" false
  (A.check_rat_assignment geQuery (point [(0, rat 37499999 100000000)]));
val _ = print "11 exported SML assignment tests passed\n";
