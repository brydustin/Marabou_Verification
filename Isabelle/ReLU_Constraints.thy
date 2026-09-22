theory ReLU_Constraints
  imports Linear_Constraints
begin

definition relu :: "real \<Rightarrow> real" where
  "relu x = max 0 x"

definition satisfies_relu :: "valuation \<Rightarrow> var \<Rightarrow> var \<Rightarrow> bool" where
  "satisfies_relu v x y \<longleftrightarrow> v y = relu (v x)"

fun satisfies_relu_constraint :: "valuation \<Rightarrow> relu_constraint \<Rightarrow> bool" where
  "satisfies_relu_constraint v (ReLU x y) = satisfies_relu v x y"

lemma relu_nonnegative [simp]: "0 \<le> relu x"
  by (simp add: relu_def)

lemma relu_zero [simp]: "relu 0 = 0"
  by (simp add: relu_def)

lemma relu_of_nonpositive: "x \<le> 0 \<Longrightarrow> relu x = 0"
  by (simp add: relu_def max_def)

lemma relu_of_nonnegative: "0 \<le> x \<Longrightarrow> relu x = x"
  by (simp add: relu_def max_def)

theorem relu_phase_decomposition:
  "y = relu x \<longleftrightarrow> (x \<le> 0 \<and> y = 0) \<or> (0 \<le> x \<and> y = x)"
  by (auto simp: relu_def max_def)

theorem satisfies_relu_phase_decomposition:
  "satisfies_relu v x y \<longleftrightarrow>
     (v x \<le> 0 \<and> v y = 0) \<or> (0 \<le> v x \<and> v y = v x)"
  by (simp add: satisfies_relu_def relu_phase_decomposition)

lemma relu_phases_overlap_iff:
  fixes v :: valuation
  shows
  "((v x \<le> 0 \<and> v y = 0) \<and> (0 \<le> v x \<and> v y = v x))
    \<longleftrightarrow> (v x = 0 \<and> v y = 0)"
  by auto

end
