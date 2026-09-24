theory Exact_Query_Format_Examples
  imports Exact_Query_Format Rational_Assignment_Examples
begin

text \<open>
  text_lines ls is the file whose lines are ls, each terminated by LF.
  Every example below is decided by the HOL decoder itself.
\<close>

definition text_lines :: "string list \<Rightarrow> bytes" where
  "text_lines ls = concat (map (\<lambda>l. ascii l @ [10]) ls)"

lemma header_only_is_the_empty_query:
  "decode_query (text_lines [''marabou-exact-query-v1'']) =
    Some \<lparr>rat_linear_atoms = [], rat_query_bounds = [], rat_relu_atoms = []\<rparr>"
  by code_simp

lemma all_statement_forms:
  "decode_query (text_lines [''marabou-exact-query-v1'',
      ''relu x0 x1'', ''eq 1 x0 1 x1 = 2'', ''lower x0 -1'',
      ''le 0.25 x2 -3/4 x0 <= -0'', ''upper x0 1'', ''ge >= 1.50'']) =
    Some \<lparr>rat_linear_atoms = [RatEq (RatExpr 0 [(1, 0), (1, 1)]) 2,
                              RatLe (RatExpr 0 [(1/4, 2), (-3/4, 0)]) 0,
                              RatGe (RatExpr 0 []) (3/2)],
          rat_query_bounds = [RatLower 0 (-1), RatUpper 0 1],
          rat_relu_atoms = [ReLU 0 1]\<rparr>"
  by code_simp

text \<open>
  The first three statements denote the query sat_rat_query from the
  assignment examples; its exact model therefore applies to these bytes.
\<close>

lemma sat_text_decodes:
  "decode_query (text_lines [''marabou-exact-query-v1'',
      ''eq 1 x0 1 x1 = 2'', ''lower x0 -1'', ''upper x0 1'', ''relu x0 x1'']) =
    Some sat_rat_query"
  by code_simp

lemma sat_text_model:
  assumes "decode_query (text_lines [''marabou-exact-query-v1'',
      ''eq 1 x0 1 x1 = 2'', ''lower x0 -1'', ''upper x0 1'', ''relu x0 x1'']) = Some Q"
  shows "satisfies_query (assignment_valuation [(0, 1), (1, 1)]) (embed_query Q)"
  using assms sat_text_decodes check_rat_assignment_sound[OF sat_rat_assignment_checked] by simp

lemma malformed_texts_rejected:
  "decode_query [] = None \<and>
   decode_query (ascii ''marabou-exact-query-v1'') = None \<and>
   decode_query (text_lines [''marabou-exact-query-v2'']) = None \<and>
   decode_query (text_lines [''marabou-exact-query-v1'', '''']) = None \<and>
   decode_query (text_lines [''marabou-exact-query-v1'', ''relu  x0 x1'']) = None \<and>
   decode_query (text_lines [''marabou-exact-query-v1'', ''relu x0 x1 '']) = None \<and>
   decode_query (text_lines [''marabou-exact-query-v1'', ''RELU x0 x1'']) = None \<and>
   decode_query (text_lines [''marabou-exact-query-v1'', ''relu x0'']) = None \<and>
   decode_query (text_lines [''marabou-exact-query-v1'', ''eq 1 x0 <= 0'']) = None \<and>
   decode_query (text_lines [''marabou-exact-query-v1'', ''eq 1 x0 1 = 0'']) = None \<and>
   decode_query (text_lines [''marabou-exact-query-v1'', ''lower x 1'']) = None \<and>
   decode_query (text_lines [''marabou-exact-query-v1'', ''lower x-1 1'']) = None \<and>
   decode_query (text_lines [''marabou-exact-query-v1'', ''lower y0 1'']) = None"
  by code_simp

lemma malformed_numbers_rejected:
  "decode_query (text_lines [''marabou-exact-query-v1'', ''lower x0 1/0'']) = None \<and>
   decode_query (text_lines [''marabou-exact-query-v1'', ''lower x0 1.'']) = None \<and>
   decode_query (text_lines [''marabou-exact-query-v1'', ''lower x0 .5'']) = None \<and>
   decode_query (text_lines [''marabou-exact-query-v1'', ''lower x0 1e3'']) = None \<and>
   decode_query (text_lines [''marabou-exact-query-v1'', ''lower x0 +1'']) = None \<and>
   decode_query (text_lines [''marabou-exact-query-v1'', ''lower x0 --1'']) = None \<and>
   decode_query (text_lines [''marabou-exact-query-v1'', ''lower x0 1/2/3'']) = None \<and>
   decode_query (text_lines [''marabou-exact-query-v1'', ''lower x0 1.5/2'']) = None \<and>
   decode_query (text_lines [''marabou-exact-query-v1'', ''lower x0 -'']) = None"
  by code_simp

text \<open>
  Carriage returns, tabs and non-ASCII bytes are not whitespace or digits.
\<close>

lemma other_bytes_rejected:
  "decode_query (ascii ''marabou-exact-query-v1'' @ [13, 10]) = None \<and>
   decode_query (text_lines [''marabou-exact-query-v1''] @ ascii ''relu x0'' @ [9] @
     ascii ''x1'' @ [10]) = None \<and>
   decode_query (text_lines [''marabou-exact-query-v1''] @ ascii ''lower x0 1'' @ [200, 10]) = None"
  by code_simp

text \<open>
  Equal rationals may be written differently; the query is the same.
  Different values give a different query, so a changed byte cannot keep
  a theorem about the original query.
\<close>

lemma number_spellings:
  "decode_query (text_lines [''marabou-exact-query-v1'', ''lower x0 0.50'']) =
     decode_query (text_lines [''marabou-exact-query-v1'', ''lower x0 2/4'']) \<and>
   decode_query (text_lines [''marabou-exact-query-v1'', ''lower x0 -0'']) =
     decode_query (text_lines [''marabou-exact-query-v1'', ''lower x0 0'']) \<and>
   decode_query (text_lines [''marabou-exact-query-v1'', ''lower x0 1/2'']) \<noteq>
     decode_query (text_lines [''marabou-exact-query-v1'', ''lower x0 1/4''])"
  by code_simp

lemma encode_sat_rat_query:
  "encode_query sat_rat_query = text_lines [''marabou-exact-query-v1'',
      ''eq 1 x0 1 x1 = 2'', ''lower x0 -1'', ''upper x0 1'', ''relu x0 x1'']"
  by code_simp

lemma sat_rat_query_round_trip:
  "decode_query (encode_query sat_rat_query) = Some sat_rat_query"
  by (rule decode_encode_query) (simp add: encodable_query_def sat_rat_query_def)

text \<open>
  The example file Isabelle/examples/relu_chain_unsat.mqx lists the captured
  chain query in another order with decimal spellings; it has exactly the
  captured constraints. A changed value, a dropped ReLU or an extra constraint
  does not, so no theorem about the capture transfers to such bytes.
\<close>

definition example_chain_lines :: "string list" where
  "example_chain_lines = [''marabou-exact-query-v1'', ''relu x0 x1'', ''relu x2 x3'',
    ''eq 1 x0 -1 x4 = 0'', ''eq 1 x2 -1 x1 = -0.25'',
    ''eq 1 x3 -1 x5 = 0'', ''lower x4 -2'', ''upper x4 -0.5'',
    ''lower x5 0.25'', ''upper x5 2'', ''lower x0 -2'', ''upper x0 2'',
    ''lower x1 0'', ''upper x1 2'', ''lower x2 -2'', ''upper x2 2'',
    ''lower x3 0'', ''upper x3 2'']"

lemma example_chain_text_decodes_like_capture:
  "decodes_like (text_lines example_chain_lines)
    Imported_Marabou_Native_Relu_Chain.imported_before_relu_query"
  by code_simp

lemma mutated_chain_texts_rejected:
  "\<not> decodes_like (text_lines (map (\<lambda>l. if l = ''upper x4 -0.5'' then ''upper x4 -0.25'' else l)
      example_chain_lines)) Imported_Marabou_Native_Relu_Chain.imported_before_relu_query \<and>
   \<not> decodes_like (text_lines (filter (\<lambda>l. l \<noteq> ''relu x2 x3'') example_chain_lines))
      Imported_Marabou_Native_Relu_Chain.imported_before_relu_query \<and>
   \<not> decodes_like (text_lines (example_chain_lines @ [''lower x6 0'']))
      Imported_Marabou_Native_Relu_Chain.imported_before_relu_query"
  by code_simp

end
