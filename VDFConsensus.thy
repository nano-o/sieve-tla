theory VDFConsensus
  imports Main "HOL-Library.FSet" "HOL-Statespace.StateSpaceSyntax"
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

inductive_set synth :: "'a msg set \<Rightarrow> 'a msg set" for msgs where
  \<comment> \<open>This is all the messages that the attacker can synthesize if it has the set of messages @{term msgs}\<close>
  "m \<in> parts msgs \<Longrightarrow> m \<in> synth msgs"
| "Val v \<in> synth msgs" \<comment> \<open>Values can be guessed\<close>
| "\<lbrakk>m1 \<in> parts msgs; m2 \<in> parts msgs\<rbrakk> \<Longrightarrow> MPair m1 m2 \<in> synth msgs"
| "\<forall> m \<in> fset s . m \<in> parts msgs \<Longrightarrow> MSet s \<in> synth msgs"

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
  fixes msgs d m
  assumes "\<And> m . m \<in> msgs \<Longrightarrow> depth m \<le> d"
    and "m \<in> synth msgs"
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
  case (3 m1 m2)
  then show ?case
    using assms(1) parts_depth by auto
next
  case (4 s)
  then show ?case
    by (metis assms(1) depth.simps(4) depth_MSet_2 less_nat_zero_code linorder_not_le parts_depth)
qed

section "The model"
   
statespace ('a, 'p, 'o) model_state =
  \<comment> \<open>@{typ 'p} is the type of player IDs\<close>
  round :: "nat" \<comment> \<open>The current round\<close>
  adv :: "'p fset" \<comment> \<open>The players controlled by the adversary in the current round\<close>
  wb :: "'p fset" \<comment> \<open>The well-behaved players in the current round\<close>
  vdf_processors :: "'p \<Rightarrow> nat" \<comment> \<open>How many parallel VDF processors a each participant has in the current round\<close>
  msgs :: "'p \<Rightarrow> 'a msg fset" \<comment> \<open>The mailbox of each player\<close>
  outputs :: "'p \<Rightarrow> 'o"

print_locale model_state

text "TODO: what about the VDFs in messages sent?"

locale model =  model_state
  where project_'a_VDFConsensus_msg_FSet_fset_'p_fun="project_'a_VDFConsensus_msg_FSet_fset_'p_fun::_ \<Rightarrow> _ \<Rightarrow> 'a msg fset"
    and inject_'o_'p_fun="inject_'o_'p_fun::('p \<Rightarrow> 'o) \<Rightarrow> _" for project_'a_VDFConsensus_msg_FSet_fset_'p_fun inject_'o_'p_fun +
    \<comment> \<open>TODO: is there a better way to capture type variables?\<close>
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

definition init where
  "init s \<equiv> s\<cdot>round = 1 \<and> s\<cdot>msgs = (\<lambda> p . {||}) \<and> vdf_assumptions s"

definition wb_msgs where
  "wb_msgs s \<equiv> let snd = (\<lambda> msgs . send_fn (s\<cdot>round) msgs) o (s\<cdot>msgs) in
    (fimage snd (s\<cdot>wb))"

definition next_round where
  "next_round s s' \<equiv>
    s'\<cdot>round = (s\<cdot>round) + 1
    \<and> vdf_assumptions s'
    \<and> s'\<cdot>msgs = (\<lambda> p . wb_msgs s) \<comment> \<open>TODO: adversarial messages\<close>
    \<and> s'\<cdot>outputs = (\<lambda> p . out (s\<cdot>round) ((s\<cdot>msgs) p))"

end

section "The Russian-doll protocol"

text \<open>Now we define a transition system modeling a distributed algorithm\<close>

text \<open>
We'll want to prove that, in a round r, no message has depth more than r, and that each player receives more
 depth-r messages from well-behaved players than from the adversary.\<close>
   
statespace ('a, 'p) vars =
  round :: "nat"
  adv :: "'p fset" \<comment> \<open>The players controlled by the adversary in the current round\<close>
  wb :: "'p fset" \<comment> \<open>The well-behaved players in the current round\<close>
  vdf_processors :: "'p \<Rightarrow> nat" \<comment> \<open>How many parallel VDF processors a each participant has in the current round\<close>
  msgs :: "'p \<Rightarrow> ('a msg) fset" \<comment> \<open>The mailbox of each participant\<close>
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

                                        
end

end