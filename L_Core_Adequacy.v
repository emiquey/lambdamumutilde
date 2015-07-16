(***************************************************************************
* Safety for Simply Typed Lambda Calculus (CBV) - Adequacy                 *
* Brian Aydemir & Arthur Chargueraud, July 2007                            *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN.

Require Import 
  L_Core_Definitions 
  L_Core_Infrastructure
  L_Core_Soundness.

(***************************************************************************)
(** * Definitions with the exists-fresh quantification *)

(** Terms are locally-closed pre-terms *)

Inductive eprf :  prf -> Prop :=
  | eprf_var : forall x,
      eprf (prf_fvar x)
  | eprf_abs : forall x p,
      x \notin fv_prf p ->
      eprf (p +^+ x) ->
      eprf (prf_abs p)
  | eprf_mu : forall a c,
      a \notin fv_clos c ->
      eclos (c *^- a) -> 
      eprf (prf_mu c )
with econt :  cont -> Prop :=
  | econt_var : forall x,
      econt (co_fvar x)
  | econt_stack : forall p e,
      eprf p->
      econt e ->
      econt (co_stack p e)
  | econt_mut : forall a c,
      a \notin fv_clos c ->
      eclos (c *^+ a) -> 
      econt (co_mut c )
with eclos : clos -> Prop :=
     | eclos_cl : forall p e,
                    eprf p -> econt e -> eclos (cl p e).

(** Typing relation *)

Reserved Notation "E |== p :+ T" (at level 69).
Reserved Notation "E |== e :- T" (at level 69).
Reserved Notation "c ::* E" (at level 69).


Inductive etyping_prf : env -> prf -> typ -> Prop :=
  | etyping_prf_var : forall E a T,
      ok E ->
      binds a (pos T) E ->
      E |== (prf_fvar a) :+ T
  | etyping_abs : forall x E U T p,
      x \notin dom E \u fv_prf p ->
      (E & x ~ pos U) |== (p +^+ x) :+ T ->
      E |== (prf_abs p) :+ (typ_arrow U T)
  | etyping_mu : forall a E T c,
      a \notin dom E \u fv_clos c ->
      (c::* E & a ~ neg T) ->
      E |== prf_mu c :+ T
with etyping_cont : env -> cont -> typ -> Prop :=
  | etyping_cont_var : forall E a T,
      ok E ->
      binds a (neg T) E ->
      E |== (co_fvar a) :- (T)
  | etyping_mut : forall a E T c,
      a \notin dom E \u fv_clos c -> 
      c*^+a :* (E & a ~ pos T) ->
      E |== (co_mut c) :- T
  | etyping_stack : forall  E U T q e,
     (E |== q :+ T ) -> 
     ( E |== e :- U ) ->
      E |== (co_stack q e) :- (typ_arrow T U)
with etyping_clos : env -> clos -> Prop :=
     | etyping_closure : forall E T p e,
        (E |== p :+ T -> E |== e :- T -> (cl p e) ::* E)
where "E |== p :+ T" := (etyping_prf E p T)
and "E |== e :- T" := (etyping_cont E e T)
and "c ::* E" := (etyping_clos E c)         .

(** Definition of values (only abstractions are values) *)

Inductive evalue : prf -> Prop :=
  | evalue_abs : forall p, 
      eprf (prf_abs p) -> evalue (prf_abs p).

(** Reduction relation - one step in call-by-value *)
Inductive ered : clos -> clos -> Prop :=
  | ered_mut : forall p c,
      econt (co_mut c) ->
      evalue p ->
      ered (cl p (co_mut c)) (c*^^+ p)
  | ered_abs : forall p q e,
      eprf (prf_abs p) -> eprf q ->
      econt e ->
      ered (cl (prf_abs p) (co_stack q e)) (cl q (co_mut (cl p e)))
  | ered_mu : forall e c ,
      eprf (prf_mu c) -> econt e ->
      ered (cl (prf_mu c) e) (c *^^- e).

Notation "c -->> c'" := (ered c c') (at level 68).

(** Goal is to prove preservation and progress *)

Definition epreservation := forall E c c',
  c ::* E ->
  c --> c' ->
   c'::* E.

Definition eprogress := forall p T, 
  empty |== p :+ T ->
     evalue p 
  \/ forall a, a\notin fv_prf p -> exists c', cl p (co_fvar a) -->> c'.



(***************************************************************************)
(** * Detailed Proofs of Renaming Lemmas (without high automation)  *)


(* ********************************************************************** *)
(** ** Proving the renaming lemma for [term]. *)

Lemma proof_rename_prf : forall x y p,
  proof (p +^+ x) ->
  x \notin fv_prf p -> 
  y \notin fv_prf p -> 
  proof (p +^+ y).
Proof.
  introv Wx Frx Fry.
  (* introduce a renaming *)
  rewrite (@subst_intro_prf_prf x). 
  (* apply substitution result *)
  SearchAbout ([ _ ~+> _ ]+ _ +^+ _).
  Print subst_prf_prf.
  apply* proof_subst_prf_prf.
  (* use the fact that x is fresh *)
  assumption.
  (* prove term (trm_fvar y) *)
  apply proof_var.
Qed.

Lemma proof_rename_cont : forall x y p,
  proof (p +^- x) ->
  x \notin fv_prf p -> 
  y \notin fv_prf p -> 
  proof (p +^- y).
Proof.
  introv Wx Frx Fry.
  (* introduce a renaming *)
  rewrite (@subst_intro_prf_cont x). 
  (* apply substitution result *)
  apply* proof_subst_prf_cont.
  (* use the fact that x is fresh *)
  assumption.
  (* prove term (trm_fvar y) *)
  apply context_var.
Qed.

Lemma context_rename_cont : forall x y e,
  context (e -^- x) ->
  x \notin fv_cont e -> 
  y \notin fv_cont e  -> 
  context (e -^- y).
Proof.
  introv Wx Frx Fry.
  (* introduce a renaming *)
  rewrite (@subst_intro_cont_cont x). 
  (* apply substitution result *)
  apply* context_subst_cont_cont.
  (* use the fact that x is fresh *)
  assumption.
  (* prove term (trm_fvar y) *)
  apply context_var.
Qed.

Lemma context_rename_prf : forall x y e,
  context (e -^+ x) ->
  x \notin fv_cont e -> 
  y \notin fv_cont e  -> 
  context (e -^+ y).
Proof.
  introv Wx Frx Fry.
  (* introduce a renaming *)
  rewrite (@subst_intro_cont_prf x). 
  (* apply substitution result *)
  apply* context_subst_cont_prf.
  (* use the fact that x is fresh *)
  assumption.
  (* prove term (trm_fvar y) *)
  apply proof_var.
Qed.


Lemma closure_rename_cont : forall x y c,
  closure (c *^- x) ->
  x \notin fv_clos c -> 
  y \notin fv_clos c  -> 
  closure (c *^- y).
Proof.
  introv Wx Frx Fry.
  (* introduce a renaming *)
  rewrite (@subst_intro_clos_cont x). 
  (* apply substitution result *)
  apply* closure_subst_clos_cont.
  (* use the fact that x is fresh *)
  assumption.
  (* prove term (trm_fvar y) *)
  apply context_var.
Qed.

Lemma closure_rename_prf : forall x y c,
  closure (c *^+ x) ->
  x \notin fv_clos c -> 
  y \notin fv_clos c  -> 
  closure (c *^+ y).
Proof.
  introv Wx Frx Fry.
  (* introduce a renaming *)
  rewrite (@subst_intro_clos_prf x). 
  (* apply substitution result *)
  apply* closure_subst_clos_prf.
  (* use the fact that x is fresh *)
  assumption.
  (* prove term (trm_fvar y) *)
  apply proof_var.
Qed.


(* ********************************************************************** *)
(** ** Proving the renaming lemma for [typing]. *)

Lemma typing_prf_rename_prf : forall x y E p U T,
  (E & x ~ pos U) |= (p +^+ x) :+ T -> 
  x \notin dom E \u fv_prf p ->
  y \notin dom E \u fv_prf p -> 
  (E & y ~ pos U) |= (p +^+ y) :+ T.
Proof.
  introv Typx Frx Fry.
  (* ensure x <> y, so as to be able to build (E & y ~ U & x ~ U) *)
  tests: (x = y). subst*.
  (* assert that E is ok *)
  lets K: (proj1 (typing_regular_prf Typx)). destruct (ok_concat_inv K).
  (* introduce substitution *)
  rewrite~ (@subst_intro_prf_prf x).
  (* apply substitution lemma *)
  Check typing_subst_prf.
  apply_empty* typing_prf_subst_prf.
  (* apply weakening lemma *)
  lets P: (@typing_prf_weaken (x ~ pos U) E (y ~ pos U)). 
   simpls. apply* P.
  (* prove (E & y ~ U |= prf_fvar y :+ U) *)
  apply* typing_prf_var.
Qed.

Lemma typing_prf_rename_cont : forall x y E p U T,
  (E & x ~ neg U) |= (p +^- x) :+ T -> 
  x \notin dom E \u fv_prf p ->
  y \notin dom E \u fv_prf p -> 
  (E & y ~ neg U) |= (p +^- y) :+ T.
Proof.
  introv Typx Frx Fry.
  (* ensure x <> y, so as to be able to build (E & y ~ U & x ~ U) *)
  tests: (x = y). subst*.
  (* assert that E is ok *)
  lets K: (proj1 (typing_regular_prf Typx)). destruct (ok_concat_inv K).
  (* introduce substitution *)
  rewrite~ (@subst_intro_prf_cont x).
  (* apply substitution lemma *)
  apply_empty* typing_prf_subst_cont.
  (* apply weakening lemma *)
  lets P: (@typing_prf_weaken (x ~ neg U) E (y ~ neg U)). 
   simpls. apply* P.
  apply* typing_cont_var.
Qed.


Lemma typing_cont_rename_prf : forall x y E e U T,
  (E & x ~ pos U) |= (e -^+ x) :- T -> 
  x \notin dom E \u fv_cont e ->
  y \notin dom E \u fv_cont e -> 
  (E & y ~ pos U) |= (e -^+ y) :- T.
Proof.
  introv Typx Frx Fry.
  (* ensure x <> y, so as to be able to build (E & y ~ U & x ~ U) *)
  tests: (x = y). subst*.
  (* assert that E is ok *)
  lets K: (proj1 (typing_regular_cont Typx)). destruct (ok_concat_inv K).
  (* introduce substitution *)
  rewrite~ (@subst_intro_cont_prf x).
  (* apply substitution lemma *)
  apply_empty* typing_cont_subst_prf.
  (* apply weakening lemma *)
  lets P: (@typing_cont_weaken (x ~ pos U) E (y ~ pos U)). 
   simpls. apply* P.
  apply* typing_prf_var.
Qed.


Lemma typing_cont_rename_cont : forall x y E e U T,
  (E & x ~ neg U) |= (e -^- x) :- T -> 
  x \notin dom E \u fv_cont e ->
  y \notin dom E \u fv_cont e -> 
  (E & y ~ neg U) |= (e -^- y) :- T.
Proof.
  introv Typx Frx Fry.
  (* ensure x <> y, so as to be able to build (E & y ~ U & x ~ U) *)
  tests: (x = y). subst*.
  (* assert that E is ok *)
  lets K: (proj1 (typing_regular_cont Typx)). destruct (ok_concat_inv K).
  (* introduce substitution *)
  rewrite~ (@subst_intro_cont_cont x).
  (* apply substitution lemma *)
  apply_empty* typing_cont_subst_cont.
  (* apply weakening lemma *)
  lets P: (@typing_cont_weaken (x ~ neg U) E (y ~ neg U)). 
   simpls. apply* P.
  apply* typing_cont_var.
Qed.


Lemma typing_clos_rename_prf : forall x y E c U,
  (c *^+ x) :* (E & x ~ pos U) -> 
  x \notin dom E \u fv_clos c ->
  y \notin dom E \u fv_clos c -> 
  (c *^+ y) :* (E & y ~ pos U).
Proof.
  introv Typx Frx Fry.
  (* ensure x <> y, so as to be able to build (E & y ~ U & x ~ U) *)
  tests: (x = y). subst*.
  (* assert that E is ok *)
  lets K: (proj1 (typing_regular_clos Typx)). destruct (ok_concat_inv K).
  (* introduce substitution *)
  rewrite~ (@subst_intro_clos_prf x).
  (* apply substitution lemma *)
  apply_empty* typing_clos_subst_prf.
  (* apply weakening lemma *)
  lets P: (@typing_clos_weaken (x ~ pos U) E (y ~ pos U)). 
   simpls. apply* P.
  apply* typing_prf_var.
Qed.


Lemma typing_clos_rename_cont : forall x y E c U,
  (c *^- x) :* (E & x ~ neg U) -> 
  x \notin dom E \u fv_clos c ->
  y \notin dom E \u fv_clos c -> 
  (c *^- y) :* (E & y ~ neg U).
Proof.
  introv Typx Frx Fry.
  (* ensure x <> y, so as to be able to build (E & y ~ U & x ~ U) *)
  tests: (x = y). subst*.
  (* assert that E is ok *)
  lets K: (proj1 (typing_regular_clos Typx)). destruct (ok_concat_inv K).
  (* introduce substitution *)
  rewrite~ (@subst_intro_clos_cont x).
  (* apply substitution lemma *)
  apply_empty* typing_clos_subst_cont.
  (* apply weakening lemma *)
  lets P: (@typing_clos_weaken (x ~ neg U) E (y ~ neg U)). 
   simpls. apply* P.
  apply* typing_cont_var.
Qed.

(***************************************************************************)
(** * Proofs of equivalence.  *)


(* ********************************************************************** *)
(** ** Proving the equivalence of [term] and [eterm] *)

Hint Constructors proof eprf.

Fixpoint proof_to_eprf p (Hp: proof p) {struct Hp}:  eprf p
with context_to_econt e (He:context e) {struct He}: econt e
with closure_to_eclos c (Hc:  closure c) {struct Hc}: eclos c.
Proof.
  - induction Hp.
    + apply eprf_var.
    + pick_fresh x. apply* (@eprf_abs x).
    + pick_fresh x. apply* (@eprf_mu x).
  - induction He.
    + apply econt_var.
    + apply econt_stack.
      * apply (proof_to_eprf p H).
      * assumption.
    + pick_fresh x. apply* (@econt_mut x).
  -induction Hc.
   apply* eclos_cl.   
Qed.

Fixpoint eprf_to_proof p (Hp: eprf p) {struct Hp}:  proof p
with econt_to_context e (He: econt e) {struct He}: context e
with eclos_to_closure c (Hc: eclos c) {struct Hc}: closure c.
Proof.
  - induction Hp.
    + apply proof_var.
    + apply_fresh proof_abs.
      apply* proof_rename_prf.
    + apply_fresh proof_mu.
      apply* closure_rename_cont.
  - induction He.
    + apply context_var.
    + apply* context_stack.
    + apply_fresh context_mut.
      apply* closure_rename_prf.
  -induction Hc.
   apply* closure_cl.   
Qed.

(* ********************************************************************** *)
(** ** Proving the equivalence of [value] and [evalue] *)

Hint Constructors value evalue.

Lemma value_to_evalue : forall p,
  value p -> evalue p.
Proof.
  lets: proof_to_eprf. induction 1; jauto.
Qed.

Lemma evalue_to_value : forall p,
  evalue p -> value p.
Proof.
  lets: eprf_to_proof. induction 1; jauto.
Qed.

(* ********************************************************************** *)
(** ** Proving the equivalence of [red] and [ered] *)

Hint Constructors red ered.

Lemma red_to_ered : forall c c',
  red c c' -> ered c c'.
Proof.
  lets: proof_to_eprf. lets: context_to_econt. lets: value_to_evalue. induction 1; jauto.
Qed.

Lemma ered_to_red : forall c c',
  ered c c' -> red c c'.
Proof.
  lets: eprf_to_proof. lets: econt_to_context. lets: evalue_to_value. induction 1; jauto.
Qed.

(* ********************************************************************** *)
(** ** Proving the equivalence of [typing] and [etyping] *)

Hint Constructors typing_prf typing_cont typing_clos.
Hint Constructors etyping_prf etyping_cont etyping_clos.

Lemma typing_to_etyping : forall E t T,
  E |= t ~: T  ->  E |== t ~: T.
Proof.
  induction 1; eauto.
  pick_fresh x. apply* (@etyping_abs x).
Qed.

Lemma etyping_to_typing : forall E t T,
  E |== t ~: T  ->  E |= t ~: T.
Proof.
  induction 1; eauto.
  apply_fresh* typing_abs as y. apply* typing_rename.   
Qed.

(* ********************************************************************** *)


