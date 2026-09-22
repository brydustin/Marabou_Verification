theory Marabou_Examples
  imports ReLU_Splitting
begin

text \<open>
  Variables 0 and 1 represent x and y. The first query says x + y = 2,
  -1 \<le> x \<le> 1, and y = ReLU(x). An exact witness is x = y = 1.
  Values of variables absent from the query do not matter.
\<close>

definition sat_example :: query where
  "sat_example = \<lparr>
     linear_atoms = [LinearEq (Linexpr 0 [(1, 0), (1, 1)]) 2],
     query_bounds = [Lower 0 (-1), Upper 0 1],
     relu_atoms = [ReLU 0 1]\<rparr>"

definition sat_witness :: valuation where
  "sat_witness = (\<lambda>_. 1)"

lemma sat_example_witness: "satisfies_query sat_witness sat_example"
  by (simp add: sat_example_def sat_witness_def satisfies_query_def
      satisfies_relu_def relu_def)

theorem sat_example_satisfiable: "satisfiable sat_example"
  unfolding satisfiable_def using sat_example_witness by blast

text \<open>
  The second query says y \<ge> 1, x \<le> 0, and y = ReLU(x).
  Prove both linear children impossible, then apply the general split rule.
  Child proofs unfold their actual syntax, so they use no remaining ReLU atom.
\<close>

definition unsat_example :: query where
  "unsat_example = \<lparr>
     linear_atoms = [LinearGe (var_expr 1) 1],
     query_bounds = [Upper 0 0],
     relu_atoms = [ReLU 0 1]\<rparr>"

lemma unsat_example_active: "unsatisfiable (active_split unsat_example 0 1)"
proof (unfold unsatisfiable_iff_no_valuation, intro allI notI)
  fix v
  assume "satisfies_query v (active_split unsat_example 0 1)"
  then have "v 1 = v 0" "v 0 \<le> 0" "1 \<le> v 1"
    by (auto simp: active_split_def unsat_example_def satisfies_query_def)
  then show False by linarith
qed

lemma unsat_example_inactive: "unsatisfiable (inactive_split unsat_example 0 1)"
proof (unfold unsatisfiable_iff_no_valuation, intro allI notI)
  fix v
  assume "satisfies_query v (inactive_split unsat_example 0 1)"
  then have "v 1 = 0" "1 \<le> v 1"
    by (auto simp: inactive_split_def unsat_example_def satisfies_query_def)
  then show False by linarith
qed

theorem unsat_example_unsatisfiable: "unsatisfiable unsat_example"
proof (rule unsatisfiable_relu_split[where x = 0 and y = 1])
  show "ReLU 0 1 \<in> set (relu_atoms unsat_example)"
    by (simp add: unsat_example_def)
  show "unsatisfiable (active_split unsat_example 0 1)" by (rule unsat_example_active)
  show "unsatisfiable (inactive_split unsat_example 0 1)" by (rule unsat_example_inactive)
qed

text \<open>The boundary valuation belongs to both children, as intended.\<close>

definition zero_example :: query where
  "zero_example = \<lparr>linear_atoms = [], query_bounds = [], relu_atoms = [ReLU 0 1]\<rparr>"

lemma zero_in_both_children:
  "satisfies_query (\<lambda>_. 0) (active_split zero_example 0 1)"
  "satisfies_query (\<lambda>_. 0) (inactive_split zero_example 0 1)"
  by (simp_all add: active_split_def inactive_split_def zero_example_def satisfies_query_def)

end
