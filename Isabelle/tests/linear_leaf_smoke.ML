(* Run from the project root after: isabelle build -e -D Isabelle
   poly --script Isabelle/tests/linear_leaf_smoke.ML
   These exercise the exported SML API, not the Isabelle proof kernel. *)

use "Isabelle/generated/Marabou_Linear_Leaf.ML";

structure Leaf = Marabou_Linear_Leaf;

fun rational (n : IntInf.int) (d : IntInf.int) =
  if d = 0 then raise Fail "zero denominator in smoke-test data"
  else Leaf.fract (Leaf.int_of_integer n) (Leaf.int_of_integer d);

val x = Leaf.nat_of_integer 0;
val zero = rational 0 1;
val one = rational 1 1;
val half = rational 1 2;
val third = rational 1 3;
val variable = Leaf.RatExpr (zero, [(one, x)]);

val bounds = Leaf.make [] [Leaf.RatLower (x, half), Leaf.RatUpper (x, third)] [];
val sign_test = Leaf.make [Leaf.RatLe (variable, zero), Leaf.RatLe (variable, one)] [] [];
val residual = Leaf.make
  [Leaf.RatLe (Leaf.RatExpr (one, [(rational 1 1000000, x)]), zero)] [] [];
val zero_margin = Leaf.make [] [Leaf.RatLower (x, half), Leaf.RatUpper (x, half)] [];
val constant = Leaf.make [Leaf.RatEq (Leaf.RatExpr (half, []), third)] [] [];

val cases =
  [("fractional contradiction", Leaf.check_linear_leaf bounds [third, third], true),
   ("negative weight", Leaf.check_linear_leaf sign_test [one, rational (~1) 1], false),
   ("nonzero residual", Leaf.check_linear_leaf residual [one], false),
   ("missing weight", Leaf.check_linear_leaf bounds [one], false),
   ("extra weight", Leaf.check_linear_leaf bounds [one, one, zero], false),
   ("zero margin", Leaf.check_linear_leaf zero_margin [one, one], false),
   ("empty query", Leaf.check_linear_leaf (Leaf.make [] [] []) [], false),
   ("constant contradiction", Leaf.check_linear_leaf constant [one, zero], true)];

val _ = List.app (fn (name, actual, expected) =>
  if actual = expected then () else raise Fail ("leaf checker: " ^ name)) cases;
val _ = print (Int.toString (length cases) ^ " exported SML checker tests passed\n");
