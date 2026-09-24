use "Isabelle/generated/Marabou_Proof_Checker.ML";

structure Tree = Marabou_Proof_Checker;
fun nat n = if n < 0 then raise Fail "negative index" else Tree.nat_of_integer n;
fun rat n d = if d = 0 then raise Fail "zero denominator"
  else Tree.fract (Tree.int_of_integer n) (Tree.int_of_integer d);
fun integer n = rat n 1;
fun leaf ns = Tree.Linear_Unsat (map integer ns);
fun expect label wanted actual =
  if wanted = actual then () else raise Fail ("failed: " ^ label);

val x = nat 0;
val y = nat 1;
val query = Tree.make [Tree.RatGe (Tree.RatExpr (integer 0, [(integer 1, y)]), integer 1)]
  [Tree.RatUpper (x, integer 0)] [Tree.ReLU (x, y)];
val active = leaf [1, 0, 1, 0, 1];
val inactive = leaf [1, 0, 1, 0, 0];
val cert = Tree.Relu_Split (x, y, active, inactive);
val _ = expect "both phases" true (Tree.check_certificate query cert);
val _ = expect "bad child" false
  (Tree.check_certificate query (Tree.Relu_Split (x, y, active, leaf [0, 0, 0, 0, 0])));
val _ = expect "absent ReLU" false
  (Tree.check_certificate query (Tree.Relu_Split (nat 2, nat 3, active, inactive)));
val _ = expect "repeated split" false
  (Tree.check_certificate query (Tree.Relu_Split (x, y, cert, cert)));
val nestedQuery = Tree.make
  [Tree.RatGe (Tree.RatExpr (integer 0, [(integer 1, y)]), integer 1)]
  [Tree.RatUpper (x, integer 0)] [Tree.ReLU (nat 2, nat 3), Tree.ReLU (x, y)];
val subtree = Tree.Relu_Split (x, y,
  leaf [1, 0, 0, 0, 1, 0, 0, 1], leaf [1, 0, 0, 0, 1, 0, 0, 0]);
val _ = expect "nested tree" true
  (Tree.check_certificate nestedQuery (Tree.Relu_Split (nat 2, nat 3, subtree, subtree)));
val upperQuery = Tree.make [] [Tree.RatUpper (x, rat 1 2), Tree.RatLower (y, rat 3 4)]
  [Tree.ReLU (x, y)];
val upperCert = Tree.Relu_Upper (x, y, rat 1 2, rat 1 2, leaf [1, 0, 1]);
val _ = expect "positive upper propagation" true (Tree.check_certificate upperQuery upperCert);
val negativeQuery = Tree.make [] [Tree.RatUpper (x, rat (~1) 2), Tree.RatLower (y, rat 1 4)]
  [Tree.ReLU (x, y)];
val _ = expect "negative upper propagation" true
  (Tree.check_certificate negativeQuery (Tree.Relu_Upper (x, y, rat (~1) 2, integer 0, leaf [1, 0, 1])));
val _ = expect "forged propagation premise" false
  (Tree.check_certificate upperQuery (Tree.Relu_Upper (x, y, integer 0, integer 0, leaf [1, 0, 1])));
val _ = expect "too strong propagation conclusion" false
  (Tree.check_certificate upperQuery (Tree.Relu_Upper (x, y, rat 1 2, rat 499999 1000000, leaf [1, 0, 1])));
val _ = expect "propagation needs ReLU membership" false
  (Tree.check_certificate (Tree.make [] [Tree.RatUpper (x, rat 1 2), Tree.RatLower (y, rat 3 4)] []) upperCert);
val _ = expect "propagation needs checked child" false
  (Tree.check_certificate upperQuery (Tree.Relu_Upper (x, y, rat 1 2, rat 1 2, leaf [0, 0, 0])));
val chainQuery = Tree.make [] [Tree.RatUpper (x, rat 1 2), Tree.RatLower (nat 2, rat 3 4)]
  [Tree.ReLU (x, y), Tree.ReLU (y, nat 2)];
val _ = expect "ordered propagation chain" true
  (Tree.check_certificate chainQuery (Tree.Relu_Upper (x, y, rat 1 2, rat 1 2,
     Tree.Relu_Upper (y, nat 2, rat 1 2, rat 1 2, leaf [1, 0, 0, 1]))));
val _ = expect "future propagation premise" false
  (Tree.check_certificate chainQuery (Tree.Relu_Upper (y, nat 2, rat 1 2, rat 1 2,
     Tree.Relu_Upper (x, y, rat 1 2, rat 1 2, leaf [0, 1, 0, 1]))));
val implicationQuery = Tree.make
  [Tree.RatEq (Tree.RatExpr (integer 0, [(rat 1 2, x), (rat 1 2, x),
      (integer (~2), nat 2), (integer 1, nat 3)]), integer 0)]
  [Tree.RatUpper (nat 2, rat 1 2), Tree.RatLower (nat 3, rat 1 2),
   Tree.RatLower (nat 2, rat (~1) 2), Tree.RatUpper (nat 3, rat 3 2)]
  [Tree.ReLU (x, y)];
val upperWeights = map integer [1, 0, 2, 1, 0, 0];
val _ = expect "linear upper implication" true
  (Tree.check_linear_bound implicationQuery (Tree.RatUpper (x, rat 1 2)) upperWeights);
val _ = expect "linear lower implication" true
  (Tree.check_linear_bound implicationQuery (Tree.RatLower (x, rat (~5) 2))
    (map integer [0, 1, 0, 0, 2, 1]));
val _ = expect "weaker bound" true
  (Tree.check_linear_bound implicationQuery (Tree.RatUpper (x, rat 5 8)) upperWeights);
val _ = expect "stronger bound" false
  (Tree.check_linear_bound implicationQuery (Tree.RatUpper (x, rat 499999 1000000)) upperWeights);
val _ = expect "implication length mismatch" false
  (Tree.check_linear_bound implicationQuery (Tree.RatUpper (x, rat 1 2))
    (map integer [1, 0, 2, 1, 0]));
val _ = expect "negative implication weight" false
  (Tree.check_linear_bound implicationQuery (Tree.RatUpper (x, rat 1 2))
    (map integer [~1, 0, 2, 1, 0, 0]));
val _ = expect "uncancelled implication coefficient" false
  (Tree.check_linear_bound implicationQuery (Tree.RatUpper (x, rat 1 2))
    (map integer [1, 0, 1, 1, 0, 0]));
val explainedQuery = Tree.make
  [Tree.RatEq (Tree.RatExpr (integer 0, [(integer 1, x), (integer (~2), nat 2),
      (integer 1, nat 3)]), integer 0)]
  [Tree.RatLower (y, rat 3 4), Tree.RatUpper (nat 2, rat 1 2),
   Tree.RatLower (nat 3, rat 1 2)] [Tree.ReLU (x, y)];
val explanation = map integer [1, 0, 0, 2, 1];
val continuation = Tree.Relu_Upper (x, y, rat 1 2, rat 1 2, leaf [0, 0, 1, 0, 1, 0, 0]);
val _ = expect "linear then ReLU then contradiction" true
  (Tree.check_certificate explainedQuery
    (Tree.Linear_Bound (Tree.RatUpper (x, rat 1 2), explanation, continuation)));
val _ = expect "forged linear premise" false
  (Tree.check_certificate explainedQuery
    (Tree.Linear_Bound (Tree.RatUpper (x, rat 1 4), explanation,
      Tree.Relu_Upper (x, y, rat 1 4, rat 1 4, leaf [0, 0, 1, 0, 1, 0, 0]))));
val _ = expect "linear bound needs checked child" false
  (Tree.check_certificate explainedQuery
    (Tree.Linear_Bound (Tree.RatUpper (x, rat 1 2), explanation, leaf [0, 0, 0, 0, 0, 0])));
val a = nat 2;
val auxiliaryEquation = Tree.RatEq
  (Tree.RatExpr (integer 0, [(integer 1, y), (integer (~1), x), (integer (~1), a)]), integer 0);
fun auxQuery lower minimumAux = Tree.make [auxiliaryEquation]
  [Tree.RatLower (x, lower), Tree.RatLower (a, minimumAux)] [Tree.ReLU (x, y)];
val pos = map integer [1, 0, 0, 0];
val neg = map integer [0, 1, 0, 0];
fun auxCert lower upper = Tree.Relu_Aux_Upper
  (x, y, a, lower, upper, pos, neg, leaf [0, 0, 1, 0, 1]);
val negativeAux = auxQuery (rat (~1) 2) (rat 3 4);
val _ = expect "negative lower to auxiliary upper" true
  (Tree.check_certificate negativeAux (auxCert (rat (~1) 2) (rat 1 2)));
val _ = expect "positive lower to zero auxiliary" true
  (Tree.check_certificate (auxQuery (rat 1 2) (rat 1 4)) (auxCert (rat 1 2) (integer 0)));
val _ = expect "zero lower to zero auxiliary" true
  (Tree.check_certificate (auxQuery (integer 0) (rat 1 4)) (auxCert (integer 0) (integer 0)));
val _ = expect "weaker auxiliary upper" true
  (Tree.check_relu_aux_upper_bound negativeAux x y a (rat (~1) 2) (rat 5 8) pos neg);
val _ = expect "auxiliary upper too strong by 1e-20" false
  (Tree.check_relu_aux_upper_bound negativeAux x y a (rat (~1) 2)
    (rat 49999999999999999999 100000000000000000000) pos neg);
val _ = expect "auxiliary equation needs positive witness" false
  (Tree.check_relu_aux_upper_bound negativeAux x y a (rat (~1) 2) (rat 1 2)
    (map integer [0, 0, 0, 0]) neg);
val _ = expect "auxiliary equation needs negative witness" false
  (Tree.check_relu_aux_upper_bound negativeAux x y a (rat (~1) 2) (rat 1 2)
    pos (map integer [0, 0, 0, 0]));
val _ = expect "auxiliary metadata cannot replace equation" false
  (Tree.check_certificate
    (Tree.make [] [Tree.RatLower (x, rat (~1) 2), Tree.RatLower (a, rat 3 4)] [Tree.ReLU (x, y)])
    (auxCert (rat (~1) 2) (rat 1 2)));
val _ = expect "unproved input lower bound" false
  (Tree.check_certificate negativeAux (auxCert (integer 0) (integer 0)));
val _ = expect "auxiliary propagation needs checked child" false
  (Tree.check_certificate negativeAux (Tree.Relu_Aux_Upper
    (x, y, a, rat (~1) 2, rat 1 2, pos, neg, leaf [0, 0, 0, 0, 0])));
val _ = expect "wrong auxiliary index" false
  (Tree.check_relu_aux_upper_bound negativeAux x y (nat 3) (rat (~1) 2) (rat 1 2) pos neg);
val _ = expect "auxiliary propagation needs ReLU membership" false
  (Tree.check_certificate
    (Tree.make [auxiliaryEquation] [Tree.RatLower (x, rat (~1) 2), Tree.RatLower (a, rat 3 4)] [])
    (auxCert (rat (~1) 2) (rat 1 2)));
fun outputQuery lower minimumAux = Tree.make [auxiliaryEquation]
  [Tree.RatLower (y, lower), Tree.RatLower (a, minimumAux)] [Tree.ReLU (x, y)];
fun outputCert lower upper = Tree.Relu_Output_Aux_Upper
  (x, y, a, lower, upper, pos, neg, leaf [0, 0, 1, 0, 1]);
val _ = expect "positive output lower forces zero auxiliary" true
  (Tree.check_certificate (outputQuery (rat 1 2) (rat 1 4)) (outputCert (rat 1 2) (integer 0)));
val _ = expect "output zero does not fix the active phase" false
  (Tree.check_certificate (outputQuery (integer 0) (integer 1)) (outputCert (integer 0) (integer 0)));
val tiny = rat 1 100000000000000000000;
val _ = expect "strictly positive exact output premise" true
  (Tree.check_certificate (outputQuery tiny (rat 1 4)) (outputCert tiny (integer 0)));
val _ = expect "negative exact output premise" false
  (Tree.check_certificate (outputQuery (rat (~1) 100000000000000000000) (rat 1 4))
    (outputCert (rat (~1) 100000000000000000000) (integer 0)));
val _ = expect "weaker output-based auxiliary cap" true
  (Tree.check_certificate (outputQuery (rat 1 2) (rat 1 4)) (outputCert (rat 1 2) (rat 1 8)));
val _ = expect "negative auxiliary cap rejected" false
  (Tree.check_relu_output_aux_upper_bound (outputQuery (rat 1 2) (integer 0))
    x y a (rat 1 2) (rat (~1) 100000000000000000000) pos neg);
val _ = expect "input bound cannot substitute for output bound" false
  (Tree.check_certificate (auxQuery (rat 1 2) (rat 1 4)) (outputCert (rat 1 2) (integer 0)));
val _ = expect "output auxiliary equation needs positive witness" false
  (Tree.check_relu_output_aux_upper_bound (outputQuery (rat 1 2) (rat 1 4))
    x y a (rat 1 2) (integer 0) (map integer [0, 0, 0, 0]) neg);
val _ = expect "output auxiliary equation needs negative witness" false
  (Tree.check_relu_output_aux_upper_bound (outputQuery (rat 1 2) (rat 1 4))
    x y a (rat 1 2) (integer 0) pos (map integer [0, 0, 0, 0]));
val _ = expect "output rule cannot trust auxiliary metadata" false
  (Tree.check_certificate
    (Tree.make [] [Tree.RatLower (y, rat 1 2), Tree.RatLower (a, rat 1 4)] [Tree.ReLU (x, y)])
    (outputCert (rat 1 2) (integer 0)));
val _ = expect "positive output alone is satisfiable" false
  (Tree.check_certificate (outputQuery (rat 1 2) (integer 0)) (outputCert (rat 1 2) (integer 0)));
val _ = expect "output rule needs a checked continuation" false
  (Tree.check_certificate (outputQuery (rat 1 2) (rat 1 4))
    (Tree.Relu_Output_Aux_Upper (x, y, a, rat 1 2, integer 0, pos, neg, leaf [0, 0, 0, 0, 0])));
fun auxLowerQuery lower minimumOutput = Tree.make [auxiliaryEquation]
  [Tree.RatLower (a, lower), Tree.RatLower (y, minimumOutput)] [Tree.ReLU (x, y)];
fun auxLowerCert lower upper = Tree.Relu_Aux_Lower_Output_Upper
  (x, y, a, lower, upper, pos, neg, leaf [0, 0, 1, 0, 1]);
val _ = expect "positive auxiliary lower forces zero output" true
  (Tree.check_certificate (auxLowerQuery (rat 1 2) (rat 1 4)) (auxLowerCert (rat 1 2) (integer 0)));
val _ = expect "zero auxiliary does not fix the inactive phase" false
  (Tree.check_certificate (auxLowerQuery (integer 0) (integer 1)) (auxLowerCert (integer 0) (integer 0)));
val _ = expect "strictly positive exact auxiliary premise" true
  (Tree.check_certificate (auxLowerQuery tiny (rat 1 4)) (auxLowerCert tiny (integer 0)));
val _ = expect "negative exact auxiliary premise" false
  (Tree.check_certificate (auxLowerQuery (rat (~1) 100000000000000000000) (rat 1 4))
    (auxLowerCert (rat (~1) 100000000000000000000) (integer 0)));
val _ = expect "weaker auxiliary-based output cap" true
  (Tree.check_certificate (auxLowerQuery (rat 1 2) (rat 1 4)) (auxLowerCert (rat 1 2) (rat 1 8)));
val _ = expect "insufficient auxiliary-based output cap" false
  (Tree.check_certificate (auxLowerQuery (rat 1 2) (rat 1 4)) (auxLowerCert (rat 1 2) (rat 1 4)));
val _ = expect "negative output cap rejected" false
  (Tree.check_relu_aux_lower_output_upper_bound (auxLowerQuery (rat 1 2) (integer 0))
    x y a (rat 1 2) (rat (~1) 100000000000000000000) pos neg);
val _ = expect "output bound cannot substitute for auxiliary bound" false
  (Tree.check_certificate (outputQuery (rat 1 2) (integer 0)) (auxLowerCert (rat 1 2) (integer 0)));
val _ = expect "input bound cannot substitute for auxiliary bound" false
  (Tree.check_certificate (auxQuery (rat 1 2) (integer 0)) (auxLowerCert (rat 1 2) (integer 0)));
val _ = expect "auxiliary lower equation needs positive witness" false
  (Tree.check_relu_aux_lower_output_upper_bound (auxLowerQuery (rat 1 2) (rat 1 4))
    x y a (rat 1 2) (integer 0) (map integer [0, 0, 0, 0]) neg);
val _ = expect "auxiliary lower equation needs negative witness" false
  (Tree.check_relu_aux_lower_output_upper_bound (auxLowerQuery (rat 1 2) (rat 1 4))
    x y a (rat 1 2) (integer 0) pos (map integer [0, 0, 0, 0]));
val _ = expect "auxiliary lower rule cannot trust auxiliary metadata" false
  (Tree.check_certificate
    (Tree.make [] [Tree.RatLower (a, rat 1 2), Tree.RatLower (y, rat 1 4)] [Tree.ReLU (x, y)])
    (auxLowerCert (rat 1 2) (integer 0)));
val _ = expect "positive auxiliary alone is satisfiable" false
  (Tree.check_certificate (auxLowerQuery (rat 1 2) (integer 0)) (auxLowerCert (rat 1 2) (integer 0)));
val _ = expect "auxiliary lower rule needs a checked continuation" false
  (Tree.check_certificate (auxLowerQuery (rat 1 2) (rat 1 4))
    (Tree.Relu_Aux_Lower_Output_Upper (x, y, a, rat 1 2, integer 0, pos, neg, leaf [0, 0, 0, 0, 0])));
val _ = expect "auxiliary lower rule needs ReLU membership" false
  (Tree.check_certificate
    (Tree.make [auxiliaryEquation] [Tree.RatLower (a, rat 1 2), Tree.RatLower (y, rat 1 4)] [])
    (auxLowerCert (rat 1 2) (integer 0)));
(* Phase fixing: weights index -y<=0, x-y<=0, then the query's rows. *)
val activeByOutput = Tree.make []
  [Tree.RatLower (x, integer (~1)), Tree.RatUpper (x, integer 1),
   Tree.RatLower (y, rat 3 2), Tree.RatUpper (y, integer 2)] [Tree.ReLU (x, y)];
fun fixActive bound weights child = Tree.Relu_Fix_Active (x, y, bound, map integer weights, child);
fun fixInactive bound weights child = Tree.Relu_Fix_Inactive (x, y, bound, map integer weights, child);
val _ = expect "positive output fixes the active phase" true
  (Tree.check_certificate activeByOutput
    (fixActive (Tree.RatLower (y, rat 3 2)) [0, 0, 0, 0, 1, 0] (leaf [1, 0, 0, 0, 1, 1, 0])));
val _ = expect "fixed phase needs a checked continuation" false
  (Tree.check_certificate activeByOutput
    (fixActive (Tree.RatLower (y, rat 3 2)) [0, 0, 0, 0, 1, 0] (leaf [0, 0, 0, 0, 1, 1, 0])));
val _ = expect "zero output lower bound does not fix the phase" false
  (Tree.check_relu_fixed_active activeByOutput x y (Tree.RatLower (y, integer 0))
    (map integer [1, 0, 0, 0, 0, 0]));
val _ = expect "tiny negative input lower bound does not fix the phase" false
  (Tree.check_relu_fixed_active activeByOutput x y (Tree.RatLower (x, rat (~1) 1000000000000))
    (map integer [0, 0, 1, 0, 0, 0]));
val _ = expect "unimplied phase premise" false
  (Tree.check_relu_fixed_active activeByOutput x y (Tree.RatLower (y, integer 2))
    (map integer [0, 0, 0, 0, 1, 0]));
val auxQuery2 = Tree.make
  [Tree.RatEq (Tree.RatExpr (integer 0, [(integer 1, y), (integer (~1), x), (integer (~1), nat 2)]), integer 0)]
  [Tree.RatLower (x, integer (~1)), Tree.RatUpper (x, integer 2), Tree.RatLower (y, integer (~1)),
   Tree.RatUpper (y, integer 2), Tree.RatLower (nat 2, integer 0), Tree.RatUpper (nat 2, integer 0)]
  [Tree.ReLU (x, y)];
val _ = expect "hull row y>=0 proves the active input bound" true
  (Tree.check_relu_fixed_active auxQuery2 x y (Tree.RatLower (x, integer 0))
    (map integer [1, 0, 1, 0, 0, 0, 0, 0, 0, 1]));
val inactiveByInput = Tree.make
  [Tree.RatEq (Tree.RatExpr (integer 0, [(integer 1, y), (integer (~1), nat 2)]), integer 0)]
  [Tree.RatLower (x, integer (~2)), Tree.RatUpper (x, rat (~1) 2), Tree.RatLower (y, integer 0),
   Tree.RatUpper (y, integer 2), Tree.RatLower (nat 2, rat 1 4), Tree.RatUpper (nat 2, integer 2)]
  [Tree.ReLU (x, y)];
val _ = expect "negative input upper bound fixes the inactive phase" true
  (Tree.check_certificate inactiveByInput
    (fixInactive (Tree.RatUpper (x, rat (~1) 2)) [0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
      (leaf [1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0])));
val _ = expect "lower bound cannot fix the inactive phase" false
  (Tree.check_relu_fixed_inactive inactiveByInput x y (Tree.RatLower (x, integer (~2)))
    (map integer [0, 0, 0, 0, 1, 0, 0, 0, 0, 0]));
val _ = expect "fixed inactive phase needs ReLU membership" false
  (Tree.check_relu_fixed_inactive inactiveByInput y x (Tree.RatUpper (x, rat (~1) 2))
    (map integer [0, 0, 0, 0, 0, 1, 0, 0, 0, 0]));
val tinyPositive = Tree.make []
  [Tree.RatLower (x, integer (~1)), Tree.RatUpper (x, rat 1 1000000000000),
   Tree.RatLower (y, rat 1 1000000000000), Tree.RatUpper (y, integer 1)] [Tree.ReLU (x, y)];
val _ = expect "tiny positive input upper bound does not fix the inactive phase" false
  (Tree.check_certificate tinyPositive
    (fixInactive (Tree.RatUpper (x, rat 1 1000000000000)) [0, 0, 0, 1, 0, 0] (leaf [1, 0, 0, 0, 0, 1, 0])));
val _ = print "72 exported SML proof-tree tests passed\n";
