(* Run from the project root after isabelle build -e -D Isabelle.
   These exercise generated code; the soundness theorems are proved in HOL. *)
use "Isabelle/generated/Marabou_Inequality_Preprocessor.ML";

structure I = Marabou_Inequality_Preprocessor;
fun nat n = if n < 0 then raise Fail "negative index" else I.nat_of_integer n;
fun integer n = I.fract (I.int_of_integer n) (I.int_of_integer 1);
fun expr terms = I.RatExpr (integer 0, map (fn (c, x) => (integer c, nat x)) terms);
fun steps xs = map (fn (i, s) => (nat i, nat s)) xs;
fun assignment xs = map (fn (x, q) => (nat x, integer q)) xs;
fun leaf ws = I.Linear_Unsat (map integer ws);
val count = ref 0;
fun expect label wanted actual =
  if actual = wanted then count := !count + 1 else raise Fail ("failed: " ^ label);
fun rejected NONE = true | rejected (SOME _) = false;

val contradictory = I.make
  [I.RatLe (expr [(1, 0)], integer 0), I.RatGe (expr [(1, 0)], integer 1)] [] [];
val certificate = leaf [1, 0, 0, 1, 1, 1];
val _ = expect "both directions and exact contradiction" true
  (I.check_after_inequality_aux_sequence contradictory (steps [(0, 1), (1, 2)]) [] [] certificate);
val _ = expect "old variable collision" false
  (I.check_after_inequality_aux_sequence contradictory (steps [(0, 0), (1, 2)]) [] [] certificate);
val _ = expect "collision with earlier slack" false
  (I.check_after_inequality_aux_sequence contradictory (steps [(0, 1), (1, 1)]) [] [] certificate);
val _ = expect "repeat transformed index" false
  (I.check_after_inequality_aux_sequence contradictory (steps [(0, 1), (0, 2)]) [] [] certificate);
val _ = expect "missing leaf weights" false
  (I.check_after_inequality_aux_sequence contradictory (steps [(0, 1), (1, 2)]) [] [] (leaf []));
val _ = expect "late out of range" true
  (rejected (I.rat_introduce_inequality_aux_sequence contradictory (steps [(0, 1), (2, 2)])));
val _ = expect "negative leaf weight" false
  (I.check_after_inequality_aux_sequence contradictory (steps [(0, 1), (1, 2)]) [] []
    (leaf [1, 0, 0, 1, ~1, 1]));

val ge = I.make [I.RatGe (expr [(1, 0)], integer 1)]
  [I.RatLower (nat 0, integer 2), I.RatUpper (nat 0, integer 2)] [];
val _ = expect "GE requires nonpositive slack" true
  (I.check_assignment_after_inequality_aux_sequence ge (steps [(0, 1)])
    (assignment [(0, 2), (1, ~1)]));
val _ = expect "incorrect positive GE slack" false
  (I.check_assignment_after_inequality_aux_sequence ge (steps [(0, 1)])
    (assignment [(0, 2), (1, 1)]));
val _ = expect "missing slack assignment" false
  (I.check_assignment_after_inequality_aux_sequence ge (steps [(0, 1)]) (assignment [(0, 2)]));
val _ = expect "wrong sign cannot refute SAT query" false
  (I.check_after_inequality_aux_sequence ge (steps [(0, 1)]) [] [] (leaf [1, 0, 1, 0, 1]));
val constant = I.make [I.RatLe (I.RatExpr (integer 1, []), integer 2)] [] [];
val _ = expect "constant expression with no old variables" true
  (I.check_assignment_after_inequality_aux_sequence constant (steps [(0, 0)]) (assignment [(0, 1)]));
val eq = I.make [I.RatEq (expr [(1, 0)], integer 0)] [] [];
val _ = expect "equality is not an inequality proposal" true
  (rejected (I.rat_introduce_inequality_aux eq (nat 0) (nat 1)));
val zeroTerm = I.make [I.RatLe (expr [(0, 7)], integer 0)] [] [];
val _ = expect "zero coefficient still reserves variable" true
  (rejected (I.rat_introduce_inequality_aux zeroTerm (nat 0) (nat 7)));
val reluOnly = I.make [I.RatLe (expr [(1, 0)], integer 0)] [] [I.ReLU (nat 7, nat 8)];
val _ = expect "ReLU-only variable collision" true
  (rejected (I.rat_introduce_inequality_aux reluOnly (nat 0) (nat 8)));
val boundOnly = I.make [I.RatLe (expr [(1, 0)], integer 0)] [I.RatUpper (nat 1, integer (~1))] [];
val _ = expect "bound-only collision cannot create contradiction" false
  (I.check_after_inequality_aux_sequence boundOnly (steps [(0, 1)]) [] [] (leaf [0, 0, 1, 1]));
val _ = print (Int.toString (!count) ^ " exported SML inequality auxiliary tests passed\n");
