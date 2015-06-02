(***************************************************************************
* Safety for Lambda Mu Mutilde (CBV) - Infrastructure                      *
* Étienne Miquey, June 2015                                                *
***************************************************************************)


(* Penser à renommer bien ! *)

Set Implicit Arguments.
Require Import LibLN.
Require Import L_Core_Definitions.
(*********************************************************************** *)
(** ** Additional Definitions used in the Proofs *)

Fixpoint size_prf (p:prf) {struct p} : nat :=
  match p with
    | prf_bvar i    => 1
    | prf_fvar a    => 1
    | prf_abs p1    => 1+(size_prf p1)
    | prf_mu c => 1+(size_clos c)
  end
with size_cont (e : cont) {struct e} : nat :=
  match e with
    | co_bvar i    => 1
    | co_fvar a    => 1
    | co_stack p f    => (size_prf p) + (size_cont f)
    | co_mut c => 1+(size_clos c)
  end
with size_clos (c:clos) {struct c} : nat :=
  match c with
    | cl p e =>  (size_prf p) + (size_cont e)
  end.


(** Computing free variables of a term. *)

Fixpoint fv_prf (p : prf) {struct p} : vars :=
  match p with
  | prf_bvar i    => \{}
  | prf_fvar a    => \{a}
  | prf_abs p1    => (fv_prf p1)
  | prf_mu c => (fv_clos c)
  end
with fv_cont (e : cont) {struct e} : vars :=
  match e with
  | co_bvar i    => \{}
  | co_fvar a    => \{a}
  | co_stack p f    => (fv_prf p) \u (fv_cont f)
  | co_mut c => (fv_clos c)
  end
with fv_clos (c:clos) {struct c} : vars :=
       match c with
         | cl p e =>  (fv_prf p) \u (fv_cont e)
       end.

(** Substitution for names *)

(* substitute z in p by q *)

Fixpoint subst_prf_prf (z : var) (p: prf) (q : prf) {struct p} : prf :=
  match p with
  | prf_bvar i    => prf_bvar i
  | prf_fvar x    => If x = z then q else (prf_fvar x)
  | prf_abs p1    => prf_abs (subst_prf_prf z p1 q)
  | prf_mu c => prf_mu (subst_clos_prf z c q) 
end
with subst_cont_prf (z : var) (e:cont) (q:prf) {struct e}:cont :=
  match e with
    | co_bvar i => co_bvar i
    | co_fvar x => co_fvar x
    | co_stack p f => co_stack (subst_prf_prf z p q) (subst_cont_prf z f q)
    | co_mut c => co_mut (subst_clos_prf z c q)
  end
with subst_clos_prf (z:var) (c:clos) (q:prf) {struct c} : clos :=
       match c with
         | cl p e =>  cl (subst_prf_prf z p q)  (subst_cont_prf z e q)
       end.

Fixpoint subst_prf_cont (z : var) (p: prf) (f : cont) {struct p} : prf :=
  match p with
  | prf_bvar i    => prf_bvar i
  | prf_fvar x    => (prf_fvar x)
  | prf_abs p1    => prf_abs (subst_prf_cont z p1 f)
  | prf_mu c => prf_mu (subst_clos_cont z c f) 
end
with subst_cont_cont (z : var) (e:cont) (f:cont) {struct e}:cont :=
  match e with
    | co_bvar i => co_bvar i
    | co_fvar x => If x=z then f else co_fvar x
    | co_stack p e1 => co_stack (subst_prf_cont z p f) (subst_cont_cont z e1 f)
    | co_mut c => co_mut (subst_clos_cont z c f)
  end
with subst_clos_cont (z:var) (c:clos) (f:cont) {struct c} : clos :=
       match c with
         | cl p e =>  cl (subst_prf_cont z p f)  (subst_cont_cont z e f)
       end.

(* UNIFORMISABLE AVEC TYPE CLASS ? *)

Notation "[ z ~+> q ]+ p" := (subst_prf_prf z p q) (at level 68).
Notation "[ z ~+> q ]- e" := (subst_cont_prf z e q) (at level 68).
Notation "[ z ~+> q ]* c" := (subst_clos_prf z c q) (at level 68).
Notation "[ z ~-> f ]+ p" := (subst_prf_cont z p f) (at level 68).
Notation "[ z ~-> f ]- e" := (subst_cont_cont z e f) (at level 68).
Notation "[ z ~-> f ]* c" := (subst_clos_cont z c f) (at level 68).
(** Definition of the body of an abstraction *)

Definition body_prf p :=
  exists L, forall x, x \notin L -> proof (p +^+ x).
Definition body_cont e :=
  exists L, forall x, x \notin L -> context (e -^+ x).
Definition body_clos e :=
  exists L, forall x, x \notin L -> closure (e *^+ x).


(* ********************************************************************** *)
(** ** Instanciation of tactics *)

(** Tactic [gather_vars] returns a set of variables occurring in
    the context of proofs, including domain of environments and
    free variables in terms mentionned in the context. *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : env => dom x) in
  let D := gather_vars_with (fun x : prf => fv_prf x) in
  let E := gather_vars_with (fun x : cont => fv_cont x) in
  let F := gather_vars_with (fun x : clos => fv_clos x) in
  constr:(A \u B \u C \u D \u E \u F).

(** Tactic [pick_fresh x] adds to the context a new variable x
    and a proof that it is fresh from all of the other variables
    gathered by tactic [gather_vars]. *)

Ltac pick_fresh Y :=
  let L := gather_vars in (pick_fresh_gen L Y).

(** Tactic [apply_fresh T as y] takes a lemma T of the form 
    [forall L ..., (forall x, x \notin L, P x) -> ... -> Q.]
    instanciate L to be the set of variables occuring in the
    context (by [gather_vars]), then introduces for the premise
    with the cofinite quantification the name x as "y" (the second
    parameter of the tactic), and the proof that x is not in L. *)

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.
Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; auto_star.
Tactic Notation "apply_fresh" constr(T) :=
  apply_fresh_base T gather_vars ltac_no_arg.
Tactic Notation "apply_fresh" "*" constr(T) :=
  apply_fresh T; auto_star.

Hint Constructors proof context closure value red.


(* ********************************************************************** *)
(** ** Properties of substitution *)

(** Substitution on indices is identity on well-formed terms. *)

Fixpoint open_rec_prf_prf_id_core p j q i r {struct p}: i <> j ->
                    {j ~+> q}+ p = {i ~+> r}+ ({j ~+> q}+ p) -> p = {i ~+> r}+ p
with open_rec_cont_prf_id_core e j q i r {struct e}: i <> j ->
                    {j ~+> q}- e = {i ~+> r}- ({j ~+> q}- e) -> e = {i ~+> r}- e
with open_rec_clos_prf_id_core c j q i r {struct c}: i <> j ->
                    {j ~+> q}* c = {i ~+> r}* ({j ~+> q}* c) -> c = {i ~+> r}* c
.
Proof.
  - revert j q i r.
    induction p; simpls;introv Neq Equ; inversion Equ;try tauto.
    + case_nat.
      * rewrite If_r;trivial.
      * exact Equ.
    + rewrite (IHp (S j) q (S i) r) at 1;
      [reflexivity | intuition | assumption].
    + now rewrite (open_rec_clos_prf_id_core c j q i r) at 1.
  - revert j q i r.
    induction e; simpls;introv Neq Equ; inversion Equ;try tauto.
    + now rewrite (open_rec_prf_prf_id_core p j q i r), (open_rec_cont_prf_id_core e j q i r) at 1. 
    + rewrite (open_rec_clos_prf_id_core c (S j) q (S i) r) at 1;
      [reflexivity | intuition | assumption].
  - destruct c as [p e];simpls;introv Neq Equ;inversion Equ.
    rewrite (open_rec_prf_prf_id_core p j q i r), (open_rec_cont_prf_id_core e j q i r) at 1;
      [reflexivity |intuition | assumption |intuition |assumption ].
Qed.

Fixpoint open_rec_prf_cont_id_core p j q i r {struct p}: i <> j ->
                    {j ~-> q}+ p = {i ~-> r}+ ({j ~-> q}+ p) -> p = {i ~-> r}+ p
with open_rec_cont_cont_id_core e j q i r {struct e}: i <> j ->
                    {j ~-> q}- e = {i ~-> r}- ({j ~-> q}- e) -> e = {i ~-> r}- e
with open_rec_clos_cont_id_core c j q i r {struct c}: i <> j ->
                    {j ~-> q}* c = {i ~-> r}* ({j ~-> q}* c) -> c = {i ~-> r}* c
.
Proof.
  - revert j q i r.
    induction p; simpls;introv Neq Equ; inversion Equ;try tauto.
    + fequals*.
    + fequals*.
  - revert j q i r.
    induction e; simpls;introv Neq Equ; inversion Equ;try tauto.
    + case_nat*. rewrite* If_r.
    + now rewrite (open_rec_prf_cont_id_core p j q i r), (open_rec_cont_cont_id_core e j q i r) at 1. 
    + rewrite (open_rec_clos_cont_id_core c (j) q (i) r) at 1;
      [reflexivity | intuition | assumption].

  - destruct c as [p e];simpls;introv Neq Equ;inversion Equ.
    rewrite (open_rec_prf_cont_id_core p j q i r), (open_rec_cont_cont_id_core e j q i r) at 1;
      [reflexivity |intuition | assumption |intuition |assumption ].
Qed.



Fixpoint open_rec_prf_prf_id_core_1 p j q i r {struct p}:
                    {j ~-> q}+ p = {i ~+> r}+ ({j ~-> q}+ p) -> p = {i ~+> r}+ p
with open_rec_cont_prf_id_core_1 e j q i r {struct e}:
                    {j ~-> q}- e = {i ~+> r}- ({j ~-> q}- e) -> e = {i ~+> r}- e
with open_rec_clos_prf_id_core_1 c j q i r {struct c}:
                    {j ~-> q}* c = {i ~+> r}* ({j ~-> q}* c) -> c = {i ~+> r}* c
.
Proof.
  - revert j q i r;induction p; simpls;intros j q i r Equ;inversion Equ;fequals*.
  - revert j q i r;induction e; simpls;intros j q i r Equ;inversion Equ;fequals*.
  - destruct c as [p e];simpls;introv Equ;inversion Equ;fequals*.
Qed.


Fixpoint open_rec_prf_cont_id_core_1 p j q i r {struct p}:
                    {j ~+> q}+ p = {i ~-> r}+ ({j ~+> q}+ p) -> p = {i ~-> r}+ p
with open_rec_cont_cont_id_core_1 e j q i r {struct e}:
                    {j ~+> q}- e = {i ~-> r}- ({j ~+> q}- e) -> e = {i ~-> r}- e
with open_rec_clos_cont_id_core_1 c j q i r {struct c}:
                    {j ~+> q}* c = {i ~-> r}* ({j ~+> q}* c) -> c = {i ~-> r}* c
.
Proof.
  - revert j q i r;induction p; simpls;intros j q i r Equ;inversion Equ;fequals*.
  - revert j q i r;induction e; simpls;intros j q i r Equ;inversion Equ;fequals*.
  - destruct c as [p e];simpls;introv Equ;inversion Equ;fequals*.
Qed.



Fixpoint open_rec_prf_prf_id (p:prf) q (H:proof p) {struct H}:
   forall k, p = {k ~+> q}+ p
with open_rec_cont_prf_id e q (H:context e) {struct H}:
   forall k, e = {k ~+> q}- e
with open_rec_clos_prf_id c q (H:closure c) {struct H}:
   forall k, c = {k ~+> q}* c.
Proof.
  - destruct H; intro k; simpl;fequal.
    + unfolds open_prf_prf.
      pick_fresh x.
      apply (@open_rec_prf_prf_id_core p 0 (prf_fvar x) (S k) q).
      * discriminate.
      * apply open_rec_prf_prf_id.
        apply* H.
    + unfolds open_clos_cont.
      pick_fresh x.
      apply (@open_rec_clos_prf_id_core_1 c 0 (co_fvar x) k ).
      apply open_rec_clos_prf_id.
      apply* H.
  -destruct H;intros;simpl;fequal.
   + apply open_rec_prf_prf_id.
     apply H.
   + apply open_rec_cont_prf_id.
     apply H0.
   + unfolds open_clos_prf.
     pick_fresh x.
     apply (@open_rec_clos_prf_id_core c 0 (prf_fvar x) (S k) ).
     * discriminate.
     * apply (open_rec_clos_prf_id).
       apply* H.

  - destruct H as [p  e Hp He];intro k;simpl;fequal;[apply open_rec_prf_prf_id|apply open_rec_cont_prf_id];assumption.
Qed.


Fixpoint open_rec_prf_cont_id (p:prf) (f:cont) (H:proof p) {struct H}:
   forall k, p = {k ~-> f}+ p
with open_rec_cont_cont_id e f (H:context e) {struct H}:
   forall k, e = {k ~-> f}- e
with open_rec_clos_cont_id c f (H:closure c) {struct H}:
   forall k, c = {k ~-> f}* c.
Proof.
  - destruct H; intro k; simpl;fequal.
    + unfolds open_prf_prf.
      pick_fresh x.
      apply (@open_rec_prf_cont_id_core_1 p 0 (prf_fvar x) (k) f).
      apply open_rec_prf_cont_id.
      apply* H.
    + unfolds open_clos_cont.
      pick_fresh x.
      apply (@open_rec_clos_cont_id_core c 0 (co_fvar x) (S k) ).
      * discriminate.
      * apply open_rec_clos_cont_id.
        apply* H.
   -destruct H;intros;simpl;fequal.
   + apply open_rec_prf_cont_id.
     apply H.
   + apply open_rec_cont_cont_id.
     apply H0.
   + unfolds open_clos_cont.
     pick_fresh x.
     apply (@open_rec_clos_cont_id_core_1 c 0 (prf_fvar x) (k) ).
     apply (open_rec_clos_cont_id).
     apply* H.
  - destruct H as [p  e Hp He];intro k;simpl;fequal;[apply open_rec_prf_cont_id|apply open_rec_cont_cont_id];assumption.
Qed.

(* Ici MIX AUSSI *)


(** Substitution for a fresh name is identity. *)

Fixpoint subst_prf_fresh x p q f{struct p}:
  x \notin fv_prf p ->  [x ~+> q]+ p = p /\ [x ~->f]+ p = p
with subst_cont_fresh x e q f{struct e}: 
       x \notin fv_cont e ->  [x ~+> q]- e = e  /\ [x ~->f]- e = e
with subst_clos_fresh x c q f{struct c}: 
       x \notin fv_clos c ->  [x ~+> q]* c = c  /\ [x ~->f]* c = c.
Proof.
  - intro Hx;destruct p; simpls.
    + split;reflexivity.
    + case_var*.
    + destruct (subst_prf_fresh x p q f Hx) as [IHx IHf];split;fequals*.
    + destruct (subst_clos_fresh x c q f Hx) as [IHx IHf];split;fequals*.
  - intro Hx;destruct e;simpls;fequals*.
    + case_var*.
    + destruct (notin_union_r Hx) as [Hpx Hex].
      destruct (subst_prf_fresh x p q f Hpx) as [IHpx IHpf] .
      destruct (subst_cont_fresh x e q f Hex) as [IHex IHef] .
      split;fequals*.
    + destruct (subst_clos_fresh x c q f Hx) as [IHcx IHcf];split;fequals*.
  - intro Hx;destruct c as [p e];simpls;fequals*.
    destruct (notin_union_r Hx) as [Hpx Hex].
    destruct (subst_prf_fresh x p q f Hpx) as [IHpx IHpf] .
    destruct (subst_cont_fresh x e q f Hex) as [IHex IHef] .
    split;fequals*.
Qed.

(* Note that [x ~-> f] could be ill-defined when x is refering to a proof-free-variable *)


(** Substitution distributes on the open operation. *)

Fixpoint subst_prf_prf_open_core x q p1 n p2  (H:proof q) : 
  [x ~+> q]+ {n ~+> p2}+ p1  = {n~+>([x ~+> q]+ p2)}+ ([x ~+> q]+ p1)
with subst_cont_prf_open_core x q e n p2 (H:proof q) : 
       [x ~+> q]- {n ~+> p2}- e  = {n~+>([x ~+> q]+ p2)}- ([x ~+> q]- e)
with subst_clos_prf_open_core x q c n p2  (H:proof q) : 
  [x ~+> q]* {n ~+> p2}* c  = {n~+>([x ~+> q]+ p2)}* ([x ~+> q]* c)                          
.
Proof.
 - generalize n.
    destruct p1; intros;simpls.
    + case_nat*.
    + case_var*.
      apply* open_rec_prf_prf_id.
    + fequals*.
    + fequals*.
 - destruct e;intros;simpls.
   + reflexivity.
   + reflexivity.
   + fequals*.
   + fequals*.
 - destruct c;intros;simpl;fequals*.
Qed.

Lemma subst_prf_prf_open:
 forall x q p1 p2, proof q -> [x ~+> q]+ p1 +^^+p2  = ([x ~+> q]+ p1) +^^+ ([x ~+> q]+ p2).
Proof.
  intros x q p1 p2 H;exact (@subst_prf_prf_open_core x q p1 0 p2 H).
Qed.

Lemma subst_cont_prf_open:
 forall x q e p2, proof q -> [x ~+> q]- e -^^+p2  = ([x ~+> q]- e) -^^+ ([x ~+> q]+ p2).
Proof.
  intros x q e p2 H;exact (@subst_cont_prf_open_core x q e 0 p2 H).
Qed.

Lemma subst_clos_prf_open:
 forall x q c p2, proof q -> [x ~+> q]* c *^^+p2  = ([x ~+> q]* c) *^^+ ([x ~+> q]+ p2).
Proof.
  intros x q c p2 H;exact (@subst_clos_prf_open_core x q c 0 p2 H).
Qed.



Fixpoint subst_prf_cont_open_core x (f:cont) p n e2 (H:context f) : 
  [x ~-> f]+ {n ~-> e2}+ p  = {n~->([x ~-> f]- e2)}+ ([x ~-> f]+ p)
with subst_cont_cont_open_core x f e n e2 (H:context f) : 
       [x ~-> f]- {n ~-> e2}- e  = {n~->([x ~-> f]- e2)}- ([x ~-> f]- e)
with subst_clos_cont_open_core x f c n e2 (H:context f) : 
  [x ~-> f]* {n ~-> e2}* c  = {n~->([x ~-> f]- e2)}* ([x ~-> f]* c)                          
.
Proof.
  - generalize n.
    destruct p; intros;simpls.
    + reflexivity.
    + reflexivity.
    + fequals*.
    + fequals*.
  - destruct e;intros;simpls.
    + case_nat*. 
    + case_var*.
      apply* open_rec_cont_cont_id.
    + fequals*.
    + fequals*.
  - destruct c;intros;simpl;fequals*.
Qed.


Lemma subst_prf_cont_open:
 forall x f p1 e2, context f -> [x ~-> f]+ p1 +^^-e2  = ([x ~-> f]+ p1) +^^- ([x ~-> f]- e2).
Proof.
  intros x f p1 e2 H;exact (@subst_prf_cont_open_core x f p1 0 e2 H).
Qed.


Lemma subst_cont_cont_open:
 forall x f e1 e2, context f -> [x ~-> f]- e1 -^^-e2  = ([x ~-> f]- e1) -^^- ([x ~-> f]- e2).
Proof.
  intros x f e1 e2 H;exact (@subst_cont_cont_open_core x f e1 0 e2 H).
Qed.

Lemma subst_clos_cont_open:
 forall x f c e2, context f -> [x ~-> f]* c *^^-e2  = ([x ~-> f]* c) *^^- ([x ~-> f]- e2).
Proof.
  intros x f c e2 H;exact (@subst_clos_cont_open_core x f c 0 e2 H).
Qed.



(* Probably true mixing prf & cont *)
(* ICI -> en profiter pour renommer : lm_name_descriptive_prf_prf *)
Fixpoint subst_open_prf_prf_core1 x q p1 n e2  (H:proof q) : 
  [x ~+> q]+ {n ~-> e2}+ p1  = {n~->([x ~+> q]- e2)}+ ([x ~+> q]+ p1)
with subst_open_cont_prf_core1 x q e n e2 (H:proof q) : 
       [x ~+> q]- {n ~-> e2}- e  = {n~->([x ~+> q]- e2)}- ([x ~+> q]- e)
with subst_open_clos_prf_core1 x q c n e2  (H:proof q) : 
  [x ~+> q]* {n ~-> e2}* c  = {n~->([x ~+> q]- e2)}* ([x ~+> q]* c)                          
.
Proof.
 - generalize n.
    destruct p1; intros;simpls.
    + reflexivity.
    + case_var*.
      apply* open_rec_prf_prf_id1.
    + fequals*.
    + fequals*.
 - destruct e;intros;simpls.
   + reflexivity.
   + reflexivity.
   + fequals*.
   + fequals*.
 - destruct c;intros;simpl;fequals*.
Qed.

Lemma subst_prf_prf_open:
 forall x q p1 p2, proof q -> [x ~+> q]+ p1 +^^+p2  = ([x ~+> q]+ p1) +^^+ ([x ~+> q]+ p2).
Proof.
  intros x q p1 p2 H;exact (@subst_prf_prf_open_core x q p1 0 p2 H).
Qed.

Lemma subst_cont_prf_open:
 forall x q e p2, proof q -> [x ~+> q]- e -^^+p2  = ([x ~+> q]- e) -^^+ ([x ~+> q]+ p2).
Proof.
  intros x q e p2 H;exact (@subst_cont_prf_open_core x q e 0 p2 H).
Qed.

Lemma subst_clos_prf_open:
 forall x q c p2, proof q -> [x ~+> q]* c *^^+p2  = ([x ~+> q]* c) *^^+ ([x ~+> q]+ p2).
Proof.
  intros x q c p2 H;exact (@subst_clos_prf_open_core x q c 0 p2 H).
Qed.



Fixpoint subst_prf_cont_open_core x (f:cont) p n e2 (H:context f) : 
  [x ~-> f]+ {n ~-> e2}+ p  = {n~->([x ~-> f]- e2)}+ ([x ~-> f]+ p)
with subst_cont_cont_open_core x f e n e2 (H:context f) : 
       [x ~-> f]- {n ~-> e2}- e  = {n~->([x ~-> f]- e2)}- ([x ~-> f]- e)
with subst_clos_cont_open_core x f c n e2 (H:context f) : 
  [x ~-> f]* {n ~-> e2}* c  = {n~->([x ~-> f]- e2)}* ([x ~-> f]* c)                          
.
Proof.
  - generalize n.
    destruct p; intros;simpls.
    + reflexivity.
    + reflexivity.
    + fequals*.
    + fequals*.
  - destruct e;intros;simpls.
    + case_nat*. 
    + case_var*.
      apply* open_rec_cont_cont_id.
    + fequals*.
    + fequals*.
  - destruct c;intros;simpl;fequals*.
Qed.


Lemma subst_prf_cont_open:
 forall x f p1 e2, context f -> [x ~-> f]+ p1 +^^-e2  = ([x ~-> f]+ p1) +^^- ([x ~-> f]- e2).
Proof.
  intros x f p1 e2 H;exact (@subst_prf_cont_open_core x f p1 0 e2 H).
Qed.


Lemma subst_cont_cont_open:
 forall x f e1 e2, context f -> [x ~-> f]- e1 -^^-e2  = ([x ~-> f]- e1) -^^- ([x ~-> f]- e2).
Proof.
  intros x f e1 e2 H;exact (@subst_cont_cont_open_core x f e1 0 e2 H).
Qed.

Lemma subst_clos_cont_open:
 forall x f c e2, context f -> [x ~-> f]* c *^^-e2  = ([x ~-> f]* c) *^^- ([x ~-> f]- e2).
Proof.
  intros x f c e2 H;exact (@subst_clos_cont_open_core x f c 0 e2 H).
Qed.


(** Substitution and open_var for distinct names commute. *)

Fixpoint subst_open_prf_prf_var x y p q (Hxy: y <> x) (Hq:proof q) {struct Hq}:
  ([x ~+> q]+ p) +^+ y = [x ~+> q]+ (p +^+ y)
with subst_open_cont_prf_var x y e q (Hxy: y <> x) (Hq:proof q) {struct Hq}:
       ([x ~+> q]- e) -^+ y = [x ~+> q]- (e -^+ y)
with subst_open_clos_prf_var x y c q (Hxy: y <> x) (Hq:proof q) {struct Hq}:
  ([x ~+> q]* c) *^+ y = [x ~+> q]* (c *^+ y).
Proof.
  rewrite* subst_prf_prf_open.
  simpl. case_var*.
  rewrite* subst_cont_prf_open.
  simpl. case_var*.
  rewrite* subst_clos_prf_open.
  simpl. case_var*.
Qed.

Fixpoint subst_open_prf_cont_var x y p f (Hxy: y <> x) (Hf:context f) {struct Hf}:
  ([x ~-> f]+ p) +^- y = [x ~-> f]+ (p +^- y)
with subst_open_cont_cont_var x y e f (Hxy: y <> x) (Hf:context f) {struct Hf}:
       ([x ~-> f]- e) -^- y = [x ~-> f]- (e -^- y)
with subst_open_clos_cont_var x y c f (Hxy: y <> x) (Hf:context f) {struct Hf}:
  ([x ~-> f]* c) *^- y = [x ~-> f]* (c *^- y).
Proof.
  rewrite* subst_prf_cont_open.
  simpl. case_var*.
  rewrite* subst_cont_cont_open.
  simpl. case_var*.
  rewrite* subst_clos_cont_open.
  simpl. case_var*.
Qed.

(* Besoin mix !!*)
Fixpoint subst_open_prf_prf_var1 x y p q (Hxy: y <> x) (Hq:proof q) {struct Hq}:
  ([x ~+> q]+ p) +^- y = [x ~+> q]+ (p +^- y)
with subst_open_cont_prf_var1 x y e q (Hxy: y <> x) (Hq:proof q) {struct Hq}:
       ([x ~+> q]- e) -^- y = [x ~+> q]- (e -^- y)
with subst_open_clos_prf_var1 x y c q (Hxy: y <> x) (Hq:proof q) {struct Hq}:
  ([x ~+> q]* c) *^- y = [x ~+> q]* (c *^- y).
Proof.
  rewrite* subst_prf_prf_open.
  simpl. case_var*.
  rewrite* subst_cont_prf_open.
  simpl. case_var*.
  rewrite* subst_clos_prf_open.
  simpl. case_var*.
Qed.


(** Opening up an abstraction of body t with a term u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Fixpoint subst_prf_prf_intro  x p q:
  x \notin (fv_prf p) -> proof q -> p +^^+ q = [x ~+> q]+ (p +^+ x)
with subst_cont_prf_intro  x e q:
  x \notin (fv_cont e) -> proof q -> e -^^+ q = [x ~+> q]- (e -^+ x)
with subst_clos_prf_intro  x c q:
  x \notin (fv_clos c) -> proof q -> c *^^+ q = [x ~+> q]* (c *^+ x)

.
Proof.
  - intros Fr Wu.
    rewrite* subst_prf_prf_open.
    destruct (@subst_prf_fresh x p q  (co_bvar 0) Fr) as [H _].
    rewrite* H.
    simpl. case_var*.
  - intros Fr Wu.
    rewrite* subst_cont_prf_open.
    destruct (@subst_cont_fresh x e q  (co_bvar 0) Fr) as [H _].
    rewrite* H.
    simpl. case_var*.
  - intros Fr Wu.
    rewrite* subst_clos_prf_open.
    destruct (@subst_clos_fresh x c q  (co_bvar 0) Fr) as [H _].
    rewrite* H.
    simpl. case_var*.
Qed.

Fixpoint subst_prf_cont_intro  x p f:
  x \notin (fv_prf p) -> context f -> p +^^- f = [x ~-> f]+ (p +^- x)
with subst_cont_cont_intro  x e f:
  x \notin (fv_cont e) -> context f -> e -^^- f = [x ~-> f]- (e -^- x)
with subst_clos_cont_intro  x c f:
  x \notin (fv_clos c) -> context f-> c *^^- f = [x ~-> f]* (c *^- x)
.
Proof.
  - intros Fr Wu.
    rewrite* subst_prf_cont_open.
    destruct (@subst_prf_fresh x p (prf_bvar 0) f Fr) as  [_ H].
    rewrite* H.
    simpl. case_var*.
  - intros Fr Wu.
    rewrite* subst_cont_cont_open.
    destruct (@subst_cont_fresh x e (prf_bvar 0) f Fr) as [_ H].
    rewrite* H.
    simpl. case_var*.
  - intros Fr Wu.
    rewrite* subst_clos_cont_open.
    destruct (@subst_clos_fresh x c (prf_bvar 0) f Fr) as [_ H].
    rewrite* H.
    simpl. case_var*.
Qed.



(* ********************************************************************** *)
(** ** Terms are stable through substitutions *)

(** Terms are stable by substitution *)

Fixpoint subst_prf_prf x p q (Hp:proof p) (Hq:proof q) {struct Hp}:
  proof ([x ~+> q]+ p)
with subst_cont_prf x e q (He:context e) (Hq:proof q) {struct He}:
  context ([x ~+> q]- e)
with subst_clos_prf x c q (Hc:closure c) (Hq:proof q) {struct Hc}:
  closure ([x ~+> q]* c).
Proof.
  - induction Hp; simpls.
    + case_var*.
    + apply_fresh (proof_abs).
      intros.
      rewrite* subst_open_prf_prf_var.
    + apply_fresh proof_mu.
      (* Besoin mix !*)
      rewrite <- subst_open_clos_cont_var.
      Guarded.
  case_var*.
  apply_fresh term_abs. rewrite* subst_open_var.
Qed.

Hint Resolve subst_term.


(* ********************************************************************** *)
(** ** Terms are stable through open *)

(** Conversion from locally closed abstractions and bodies *)

Lemma term_abs_to_body : forall t1, 
  term (trm_abs t1) -> body t1.
Proof. intros. unfold body. inversion* H. Qed.

Lemma body_to_term_abs : forall t1, 
  body t1 -> term (trm_abs t1).
Proof. intros. inversion* H. Qed.

Hint Resolve term_abs_to_body body_to_term_abs.

(** ** Opening a body with a term gives a term *)

Lemma open_term : forall t u,
  body t -> term u -> term (t ^^ u).
Proof.
  intros. destruct H. pick_fresh y. rewrite* (@subst_intro y).
Qed.

Hint Resolve open_term.


(* ********************************************************************** *)
(** ** Regularity of relations *)

(** A typing relation holds only if the environment has no
   duplicated keys and the pre-term is locally-closed. *)

Lemma typing_regular : forall E e T,
  typing E e T -> ok E /\ term e.
Proof.
  split; induction* H. 
  pick_fresh y. forwards~ : (H0 y).
Qed.

(** The value predicate only holds on locally-closed terms. *)

Lemma value_regular : forall e,
  value e -> term e.
Proof.
  induction 1; autos*.
Qed.

(** A reduction relation only holds on pairs of locally-closed terms. *)

Lemma red_regular : forall e e',
  red e e' -> term e /\ term e'.
Proof.
  induction 1; autos* value_regular.
Qed.

(** Automation for reasoning on well-formedness. *)

Hint Extern 1 (ok ?E) =>
  match goal with
  | H: typing E _ _ |- _ => apply (proj1 (typing_regular H))
  end.

Hint Extern 1 (term ?t) =>
  match goal with
  | H: typing _ t _ |- _ => apply (proj2 (typing_regular H))
  | H: red t _ |- _ => apply (proj1 (red_regular H))
  | H: red _ t |- _ => apply (proj2 (red_regular H))
  | H: value t |- _ => apply (value_regular H)
  end.
