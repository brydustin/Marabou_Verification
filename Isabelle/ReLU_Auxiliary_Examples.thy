theory ReLU_Auxiliary_Examples
  imports Rational_ReLU_Auxiliary Imported_Marabou_Source_Relu_Aux
begin

text \<open>
  Start before the ReLU auxiliary in the earlier relu_aux capture. This
  four-variable query is explicit HOL data. The checked introduction gives
  exactly the already captured five-variable source, in its original term
  order. The actual capture supplied that auxiliary beforehand; no native
  execution of transformToUseAuxVariables or new solver run is claimed here.
\<close>

definition solver_before_relu_aux :: rat_query where
  "solver_before_relu_aux = \<lparr>
    rat_linear_atoms = [RatEq (RatExpr 0 [(1, 0), (-1, 2)]) 0,
      RatEq (RatExpr 0 [(1, 1), (-1, 3)]) 0],
    rat_query_bounds = [RatLower 0 (-2), RatUpper 0 2,
      RatLower 1 0, RatUpper 1 2, RatLower 2 (-2), RatUpper 2 (-1/2),
      RatLower 3 (1/4), RatUpper 3 2],
    rat_relu_atoms = [ReLU 0 1]\<rparr>"

lemma solver_relu_aux_matches_captured_source:
  "rat_introduce_relu_aux solver_before_relu_aux 0 1 4 (Some (-2)) =
    Some imported_source_query"
  by code_simp

theorem solver_relu_aux_source_equisatisfiable:
  "satisfiable (embed_query imported_source_query) \<longleftrightarrow>
    satisfiable (embed_query solver_before_relu_aux)"
  by (rule rat_introduce_relu_aux_satisfiable_iff[OF solver_relu_aux_matches_captured_source])

lemma solver_before_relu_aux_checked:
  "check_after_relu_aux solver_before_relu_aux 0 1 4 (Some (-2))
    imported_steps imported_certificate"
  by code_simp

theorem solver_before_relu_aux_unsatisfiable:
  "unsatisfiable (embed_query solver_before_relu_aux)"
  by (rule check_after_relu_aux_sound[OF solver_before_relu_aux_checked])

lemma solver_relu_aux_rejects_bad_bridge_or_proof:
  "\<not> check_after_relu_aux solver_before_relu_aux 0 1 4 (Some 0)
      imported_steps imported_certificate \<and>
   \<not> check_after_relu_aux solver_before_relu_aux 0 1 4 (Some (-2))
      (take 2 imported_steps) imported_certificate \<and>
   \<not> check_after_relu_aux solver_before_relu_aux 0 1 4 (Some (-2))
      imported_steps (Linear_Unsat [])"
  by code_simp

text \<open>
  Negative, zero, and positive input lower bounds, and no finite bound.
  A fresh auxiliary can change a valuation without changing satisfiability.
\<close>

definition relu_interval_query :: "rat \<Rightarrow> rat \<Rightarrow> rat_query" where
  "relu_interval_query l u = \<lparr>rat_linear_atoms = [],
    rat_query_bounds = [RatLower 0 l, RatUpper 0 u], rat_relu_atoms = [ReLU 0 1]\<rparr>"

definition negative_relu_aux_result :: rat_query where
  "negative_relu_aux_result = \<lparr>
    rat_linear_atoms = [RatEq (RatExpr 0 [(1, 1), (-1, 0), (-1, 2)]) 0],
    rat_query_bounds = [RatLower 0 (-3/2), RatUpper 0 (-1/2),
      RatLower 2 0, RatUpper 2 (3/2)], rat_relu_atoms = [ReLU 0 1]\<rparr>"

lemma negative_relu_aux_introduction:
  "rat_introduce_relu_aux (relu_interval_query (-3/2) (-1/2)) 0 1 2 (Some (-3/2)) =
    Some negative_relu_aux_result"
  by code_simp

definition negative_relu_witness :: valuation where
  "negative_relu_witness i = (if i = 0 then -1 else if i = 2 then 17 else 0)"

lemma negative_relu_source_has_model:
  "satisfies_query negative_relu_witness (embed_query (relu_interval_query (-3/2) (-1/2)))"
  by (simp add: negative_relu_witness_def relu_interval_query_def embed_query_def
      satisfies_query_def satisfies_relu_def relu_def of_rat_divide of_rat_minus)

lemma negative_relu_aux_extended_model:
  "satisfies_query (negative_relu_witness(2 := 1)) (embed_query negative_relu_aux_result)"
  using rat_relu_aux_model_extension[OF negative_relu_aux_introduction, of negative_relu_witness]
    negative_relu_source_has_model
  by (simp add: negative_relu_witness_def)

lemma negative_relu_aux_needs_extension:
  "\<not> satisfies_query negative_relu_witness (embed_query negative_relu_aux_result)"
  by (simp add: negative_relu_witness_def negative_relu_aux_result_def embed_query_def
      satisfies_query_def of_rat_divide)

theorem negative_relu_source_rejects_all_certificates:
  "\<not> check_after_relu_aux (relu_interval_query (-3/2) (-1/2)) x y a lower steps cert"
  by (rule check_after_relu_aux_rejects_model[OF negative_relu_source_has_model])

lemma zero_relu_aux_introduction:
  "rat_introduce_relu_aux (relu_interval_query 0 0) 0 1 2 (Some 0) =
    Some \<lparr>rat_linear_atoms = [RatEq (RatExpr 0 [(1, 1), (-1, 0), (-1, 2)]) 0],
      rat_query_bounds = [RatLower 0 0, RatUpper 0 0, RatLower 2 0, RatUpper 2 0],
      rat_relu_atoms = [ReLU 0 1]\<rparr>"
  by code_simp

lemma positive_relu_aux_introduction:
  "rat_introduce_relu_aux (relu_interval_query (3/2) 2) 0 1 2 (Some (3/2)) =
    Some \<lparr>rat_linear_atoms = [RatEq (RatExpr 0 [(1, 1), (-1, 0), (-1, 2)]) 0],
      rat_query_bounds = [RatLower 0 (3/2), RatUpper 0 2, RatLower 2 0, RatUpper 2 0],
      rat_relu_atoms = [ReLU 0 1]\<rparr>"
  by code_simp

definition unbounded_relu_source :: rat_query where
  "unbounded_relu_source = \<lparr>rat_linear_atoms = [], rat_query_bounds = [],
    rat_relu_atoms = [ReLU 0 1]\<rparr>"

definition unbounded_relu_aux_result :: rat_query where
  "unbounded_relu_aux_result = \<lparr>
    rat_linear_atoms = [RatEq (RatExpr 0 [(1, 1), (-1, 0), (-1, 2)]) 0],
    rat_query_bounds = [RatLower 2 0], rat_relu_atoms = [ReLU 0 1]\<rparr>"

lemma unbounded_relu_aux_introduction:
  "rat_introduce_relu_aux unbounded_relu_source 0 1 2 None = Some unbounded_relu_aux_result"
  by code_simp

lemma unbounded_relu_aux_has_model:
  "satisfies_query (\<lambda>i. if i = 0 then -100 else if i = 2 then 100 else 0)
    (embed_query unbounded_relu_aux_result)"
  by (simp add: unbounded_relu_aux_result_def embed_query_def satisfies_query_def
      satisfies_relu_def relu_def)

lemma same_input_output_is_supported:
  "rat_introduce_relu_aux
    \<lparr>rat_linear_atoms = [], rat_query_bounds = [RatLower 0 0], rat_relu_atoms = [ReLU 0 0]\<rparr>
      0 0 1 (Some 0) =
   Some \<lparr>rat_linear_atoms = [RatEq (RatExpr 0 [(1, 0), (-1, 0), (-1, 1)]) 0],
     rat_query_bounds = [RatLower 0 0, RatLower 1 0, RatUpper 1 0],
     rat_relu_atoms = [ReLU 0 0]\<rparr>"
  by code_simp

text \<open>
  Freshness covers all query components, including zero-coefficient terms
  and unrelated ReLUs. The selected lower bound must actually be present;
  an upper bound or an implied but absent lower bound is not accepted.
\<close>

definition occupied_relu_source :: rat_query where
  "occupied_relu_source = \<lparr>
    rat_linear_atoms = [RatLe (RatExpr 0 [(0, 9), (1, 2)]) 3],
    rat_query_bounds = [RatLower 4 (-2)],
    rat_relu_atoms = [ReLU 0 1, ReLU 7 8]\<rparr>"

lemma relu_aux_rejects_all_syntactic_collisions:
  "\<forall>a \<in> set [0, 1, 2, 4, 7, 8, 9].
    rat_introduce_relu_aux occupied_relu_source 0 1 a None = None"
  by code_simp

lemma relu_aux_rejects_reused_auxiliary:
  "rat_introduce_relu_aux
    (rat_relu_aux_query occupied_relu_source 0 1 5 None) 0 1 5 None = None"
  by code_simp

lemma relu_aux_rejects_missing_premises:
  "rat_introduce_relu_aux occupied_relu_source 1 0 5 None = None \<and>
   rat_introduce_relu_aux occupied_relu_source 0 1 5 (Some (-2)) = None \<and>
   rat_introduce_relu_aux (relu_interval_query (-3/2) (-1/2)) 0 1 2 (Some 0) = None \<and>
   rat_introduce_relu_aux (relu_interval_query (-3/2) (-1/2)) 0 1 2 (Some (-1/2)) = None \<and>
   rat_introduce_relu_aux (relu_interval_query (-3/2) (-1/2)) 0 1 2 (Some (-10)) = None \<and>
   rat_introduce_relu_aux unbounded_relu_source 0 1 2 (Some 0) = None"
  by code_simp

text \<open>
  Designed negative controls: dropping freshness or ReLU membership can make
  a satisfiable source inconsistent. Valid linear certificates of those raw
  results do not pass the guarded interface. These are not solver failures.
\<close>

definition relu_collision_result :: rat_query where
  "relu_collision_result = rat_relu_aux_query (relu_interval_query (-1) (-1)) 0 1 1 (Some (-1))"

lemma relu_collision_source_has_model:
  "satisfies_query (\<lambda>i. if i = 0 then -1 else 0)
    (embed_query (relu_interval_query (-1) (-1)))"
  by (simp add: relu_interval_query_def embed_query_def satisfies_query_def
      satisfies_relu_def relu_def)

lemma relu_collision_result_checked:
  "check_certificate relu_collision_result (Linear_Unsat [1, 0, 0, 1, 0, 0])"
  by code_simp

theorem relu_collision_raw_result_unsatisfiable:
  "unsatisfiable (embed_query relu_collision_result)"
  by (rule check_certificate_sound[OF relu_collision_result_checked])

lemma relu_collision_cannot_certify_source:
  "rat_introduce_relu_aux (relu_interval_query (-1) (-1)) 0 1 1 (Some (-1)) = None \<and>
   \<not> check_after_relu_aux (relu_interval_query (-1) (-1)) 0 1 1 (Some (-1))
     [] (Linear_Unsat [1, 0, 0, 1, 0, 0])"
  by code_simp

definition no_relu_source :: rat_query where
  "no_relu_source = \<lparr>rat_linear_atoms = [],
    rat_query_bounds = [RatLower 0 1, RatUpper 1 0], rat_relu_atoms = []\<rparr>"

lemma no_relu_source_has_model:
  "satisfies_query (\<lambda>i. if i = 0 then 1 else 0) (embed_query no_relu_source)"
  by (simp add: no_relu_source_def embed_query_def satisfies_query_def)

lemma no_relu_raw_result_checked:
  "check_certificate (rat_relu_aux_query no_relu_source 0 1 2 None)
    (Linear_Unsat [0, 1, 1, 1, 1])"
  by code_simp

theorem no_relu_raw_result_unsatisfiable:
  "unsatisfiable (embed_query (rat_relu_aux_query no_relu_source 0 1 2 None))"
  by (rule check_certificate_sound[OF no_relu_raw_result_checked])

lemma missing_relu_cannot_certify_source:
  "rat_introduce_relu_aux no_relu_source 0 1 2 None = None \<and>
   \<not> check_after_relu_aux no_relu_source 0 1 2 None [] (Linear_Unsat [0, 1, 1, 1, 1])"
  by code_simp

end
