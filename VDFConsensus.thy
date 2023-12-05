theory VDFConsensus
  imports Main "HOL-Library.FSet" "HOL-Statespace.StateSpaceSyntax" "HOL-Library.State_Monad"
begin

section "Messages"

text \<open>First we define a datatype of messages.\<close>

datatype 'a msg = 
  Val 'a \<comment> \<open>A guessable value\<close>
| Nonce nat \<comment> \<open>A non-guessable nonce\<close>
| VDF "'a msg" \<comment> \<open>The VDF applied to a given message\<close>
| MSet "('a msg) fset" \<comment> \<open>A (finite) set of messages packed together in one message\<close>
| MPair "'a msg" "'a msg" \<comment> \<open>A pair of two messages\<close>

subsection "The depth of a message"

text \<open>The depth of a message is the length of the longest VDF chain appearing in the message.\<close>

primrec depth :: "'a msg \<Rightarrow> nat" where
  "depth (Val x) = 0"
| "depth (Nonce n) = 0"
| "depth (VDF m) = depth m + 1"
| "depth (MSet s) = (if s = {||} then 0 else (fMax (fimage depth s)))" \<comment> \<open>This is the max depth of messages in the set @{term s}\<close>
| "depth (MPair m1 m2) = Orderings.max (depth m1) (depth m2)"

lemma depth_MSet_1: "m \<in> fset s \<Longrightarrow> depth m \<le> depth (MSet s)"
  by auto

lemma depth_MSet_2: "s \<noteq> {||} \<Longrightarrow> \<exists> m . m \<in> fset s \<and> depth (MSet s) = depth m"
  by (auto; metis fMax_in fempty_iff fempty_is_fimage fimageE)

text \<open>Example\<close>

lemma "depth (VDF (MSet {| VDF (Val 0), VDF (VDF (Val 42)) |})) = 3"
  by simp

subsection "Messages that the adversary can forge"

inductive_set parts :: "'a msg set \<Rightarrow> 'a msg set" for msgs where
  \<comment> \<open>All the parts that can be extracted from the set of messages @{term msgs}\<close>
  "m \<in> msgs \<Longrightarrow> m \<in> parts msgs"
| "MPair m1 m2 \<in> parts msgs \<Longrightarrow> m1 \<in> parts msgs"
| "MPair m1 m2 \<in> parts msgs \<Longrightarrow> m2 \<in> parts msgs"
| "\<lbrakk>MSet s \<in> parts msgs; m \<in> fset s\<rbrakk> \<Longrightarrow> m \<in> parts msgs"

inductive_set synth :: "'a msg set \<Rightarrow> nat set \<Rightarrow> 'a msg set" for msgs nonces where
  \<comment> \<open>This is all the messages that the attacker can synthesize if it has the set of messages @{term msgs},
    where @{term nonces} is the set of nonces that have already been used\<close>
  "m \<in> parts msgs \<Longrightarrow> m \<in> synth msgs nonces"
| "Val v \<in> synth msgs nonces" \<comment> \<open>Values can be guessed\<close>
| "n \<notin> nonces \<Longrightarrow> Nonce n \<in> synth msgs nonces"
| "\<lbrakk>m1 \<in> parts msgs; m2 \<in> parts msgs\<rbrakk> \<Longrightarrow> MPair m1 m2 \<in> synth msgs nonces"
| "\<forall> m \<in> fset s . m \<in> parts msgs \<Longrightarrow> MSet s \<in> synth msgs nonces"

definition synth_vdf where
  \<comment> \<open>The messages that the adversary can synthesis if it can compute one VDF output\<close>
  "synth_vdf msgs nonces \<equiv> let syn = synth msgs nonces in
    \<Union> m \<in> syn . synth (syn \<union> {VDF m}) nonces"

lemma parts_depth:
  fixes msgs d m
  assumes "\<And> m . m \<in> msgs \<Longrightarrow> depth m \<le> d"
    and "m \<in> parts msgs"
  shows "depth m \<le> d" 
  using assms(2)
proof (induct m)
  case (1 m)
  then show ?case
    by (simp add: assms(1))
next
  case (2 m1 m2)
  then show ?case
    by simp
next
  case (3 m1 m2)
  then show ?case by simp
next
  case (4 s m)
  then show ?case
    using depth_MSet_1 by fastforce
qed


text \<open>
Main lemma: the adversary cannot forge a message that has larger depth than any message it already has.\<close>

lemma synth_depth:
  fixes msgs d m nonces
  assumes "\<And> m . m \<in> msgs \<Longrightarrow> depth m \<le> d"
    and "m \<in> synth msgs nonces"
  shows "depth m \<le> d" 
  using assms(2)
proof (induct m)
  case (1 m)
  then show ?case
    using assms(1) parts_depth by auto
next
  case (2 v)
  then show ?case
    by simp 
next
  case (3 n)
  then show ?case
    by auto 
next
  case (4 m1 m2)
  then show ?case
    using assms(1) parts_depth by auto
next
  case (5 s)
  then show ?case
    by (metis assms(1) depth.simps(4) depth_MSet_2 less_nat_zero_code linorder_not_le parts_depth)
qed

lemma synth_vdf_depth:
  fixes msgs :: "'a msg set" and m :: "'a msg" and d :: nat and nonces
  assumes "\<And> m . m \<in> msgs \<Longrightarrow> depth m \<le> d"
    and "m \<in> synth_vdf msgs nonces"
  shows "depth m \<le> d+1"
proof -
  have "depth m \<le> d+1" if "m \<in> synth (synth msgs nonces \<union> {VDF m'}) nonces" and "m' \<in> synth msgs nonces" for m m'
  proof -
    have "depth m' \<le> d"
      using assms(1) synth_depth that(2) by blast
    hence "depth m'' \<le> d+1" if "m'' \<in> synth msgs nonces \<union> {VDF m'}" for m''
      by (metis Suc_eq_plus1 Un_iff assms(1) depth.simps(3) not_less_eq_eq singleton_iff synth_depth that trans_le_add1)
    thus ?thesis
      by (meson synth_depth that(1)) 
  qed
  thus ?thesis using assms(2)
    unfolding synth_vdf_def
    by (auto simp add:Let_def)
qed

section "The model"

statespace ('a, 'p, 'o) model_state =
  \<comment> \<open>@{typ 'p} is the type of player IDs\<close>
  round :: "nat" \<comment> \<open>The current round\<close>
  adv :: "'p fset" \<comment> \<open>The players controlled by the adversary in the current round\<close>
  wb :: "'p fset" \<comment> \<open>The well-behaved players in the current round\<close>
  vdf_processors :: "'p \<Rightarrow> nat" \<comment> \<open>How many parallel VDF processors a each participant has in the current round\<close>
  msgs :: "'p \<Rightarrow> 'a msg fset" \<comment> \<open>The mailbox of each player. TODO: probably need the sender.\<close>
  outputs :: "'p \<Rightarrow> 'o"
  adv_knowledge :: "'a msg set" \<comment> \<open>The information that the adversary collected, i.e. all messages ever sent\<close>
  prev_msgs :: "'p \<Rightarrow> 'p \<Rightarrow> 'a msg fset" \<comment> \<open>A history variable tracking the messages sent in the previous round\<close>
  nonces :: "nat set" \<comment> \<open>set of nonces used\<close>

locale model =  model_state
  \<comment> \<open>Hack to fix type variable names; is there a better way? Note that a state has type @{typ "'name => 'value"}\<close>
  where project_'a_VDFConsensus_msg_FSet_fset_'p_fun="project_'a_VDFConsensus_msg_FSet_fset_'p_fun::'value \<Rightarrow> 'p \<Rightarrow> 'a msg fset"
    and inject_'o_'p_fun="inject_'o_'p_fun::('p \<Rightarrow> 'o) \<Rightarrow> _"
    and round="round::'name" for project_'a_VDFConsensus_msg_FSet_fset_'p_fun inject_'o_'p_fun round +
  fixes send_fn :: "nat \<Rightarrow> 'a msg fset \<Rightarrow> 'a msg" \<comment> \<open>Determines what message a well-behaved player sends each round, as a function of the messages it receives\<close>
    and out :: "nat \<Rightarrow> 'a msg fset \<Rightarrow> 'o" \<comment> \<open>Determines an output each round\<close>
begin

definition vdf_assumptions where
  "vdf_assumptions s \<equiv> 
    fsum (s\<cdot>vdf_processors) (s\<cdot>adv) < fsum (s\<cdot>vdf_processors) (s\<cdot>wb)
      \<comment> \<open>Adversary has less VDF processors than well-behaved players have\<close>
    \<and> (s\<cdot>wb) \<noteq> {||}
      \<comment> \<open>At least one well-behaved player\<close>
    \<and> fsum (s\<cdot>vdf_processors) (s\<cdot>wb) > 0
      \<comment> \<open>Well-behaved players can compute at least 1 VDF output\<close>"

definition wb_msg where
  "wb_msg s p \<equiv> let n = SOME nonce . nonce \<notin> (s\<cdot>nonces); m = VDF (MPair (Nonce n) (MSet ((s\<cdot>msgs) p))) in
      \<comment> \<open>We just pack all the messages received along with a fresh nonce in a VDF\<close>
      s<nonces := (s\<cdot>nonces) \<union> {n}, msgs := \<lambda> p . (s\<cdot>msgs) p |\<union>| {|m|}>"

text \<open>TODO: fix starting from here\<close>

(*
definition wb_send_msgs where
  "wb_send_msgs s \<equiv> ffold (\<lambda> p s . wb_send_msg p s) s (s\<cdot>wb)" *)

definition adv_msgs where
  \<comment> \<open>This is the possible set of messages that the adversary can send each round\<close>
  "adv_msgs s \<equiv> {msgs . \<exists> vdf_msgs . 
    vdf_msgs \<subseteq> synth_vdf (s\<cdot>adv_knowledge) (s\<cdot>nonces)
    \<and> card vdf_msgs \<le> fsum (s\<cdot>vdf_processors) (s\<cdot>adv)
    \<and> msgs = synth (s\<cdot>adv_knowledge) (s\<cdot>nonces) \<union> vdf_msgs}"

definition init where
  "init s \<equiv> s\<cdot>round = 1 \<and> s\<cdot>msgs = (\<lambda> p . {||}) \<and> vdf_assumptions s \<and> (s\<cdot>adv_knowledge) = {}
    \<and> (s\<cdot>nonces) = {}"

definition next_round where
  "next_round s s' \<equiv>
    s'\<cdot>round = (s\<cdot>round) + 1
    \<and> vdf_assumptions s'
    \<and> (\<exists> ms . (\<forall> p . fset (ms p) \<subseteq> synth_vdf (s\<cdot>adv_knowledge) {})
        \<and> s'\<cdot>msgs = (\<lambda> p . (s\<cdot>msgs) p |\<union>| ms p))
    \<and> s'\<cdot>outputs = (\<lambda> p . out (s\<cdot>round) ((s\<cdot>msgs) p))
    \<and> s'\<cdot>adv_knowledge = (s\<cdot>adv_knowledge) \<union> (\<Union> p . fset ((s'\<cdot>msgs) p))"

end

(*
section "The Russian-doll protocol"

text \<open>Now we define a transition system modeling a distributed algorithm\<close>

text \<open>
We'll want to prove that, in a round r, no message has depth more than r, and that each player receives more
 depth-r messages from well-behaved players than from the adversary.\<close>
   
statespace ('a, 'p) vars =
  round :: "nat"
  adv :: "'p set" \<comment> \<open>The players controlled by the adversary in the current round\<close>
  wb :: "'p set" \<comment> \<open>The well-behaved players in the current round\<close>
  vdf_processors :: "'p \<Rightarrow> nat" \<comment> \<open>How many parallel VDF processors a each participant has in the current round\<close>
  msgs :: "'p \<Rightarrow> ('a msg) set" \<comment> \<open>The mailbox of each participant\<close>
  round_done :: "'p \<Rightarrow> bool" \<comment> \<open>Whether a process has taken a step this round\<close>

context vars
begin

definition init where
  "init s \<equiv> s\<cdot>round = 1 \<and> (\<forall> p . \<not> (s\<cdot>round_done) p)"

definition next_round where
  "next_round s s' \<equiv>
    (\<forall> p \<in> fset ((s\<cdot>adv) |\<union>| (s\<cdot>wb)) . (s\<cdot>round_done) p)
    \<and> (\<exists> a w . w \<noteq> {||} \<and> fcard w > fcard a \<and>
        s' = s<round := (s\<cdot>round) + 1, adv := a, wb := w, round_done := \<lambda> p . False>)"

definition trans_rel where
  "trans_rel s s' \<equiv> next_round s s'"

definition inductive_invariant where
  "inductive_invariant P \<equiv>
    (\<forall> s . init s \<longrightarrow> P s) \<and> (\<forall> s s' . P s \<and> trans_rel s s' \<longrightarrow> P s')"

declare inductive_invariant_def[simp]
declare trans_rel_def[simp]
declare next_round_def[simp]
declare init_def[simp]

lemma round_ge_1:
  "inductive_invariant (\<lambda> s . (s\<cdot>round) \<ge> 1)" by auto

                                        
end *)

end