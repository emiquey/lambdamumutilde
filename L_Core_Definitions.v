(***************************************************************************
* Safety for Simply Typed Lambda Calculus (CBV) - Definitions              *
* Brian Aydemir & Arthur Chargueraud, July 2007                            *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN.
Implicit Types x : var.

(** Grammar of types. *)

Inductive typ : Set :=
| typ_var   : var -> typ
| typ_arrow : typ -> typ -> typ
| typ_mu :  typ.


(* Inductive cotyp : Set :=
 | neg : typ -> cotyp.
 *)

 Inductive ltyp : Set :=
 | pos: typ -> ltyp
 | neg: typ -> ltyp.
(*
| cotyp_var : var -> cotyp
| cotyp_arrow : typ -> cotyp -> cotyp
| cotyp_mut : cotyp.
*)

(** Grammar of pre-terms. *)

Inductive prf : Type :=
| prf_bvar : nat -> prf (* bound variable in de Bruijn style *)
| prf_fvar : var -> prf (* free variable in named style *)
| prf_abs  : prf -> prf
| prf_mu  :  clos-> prf
with cont:Type :=
| co_bvar: nat -> cont
| co_fvar: var -> cont
| co_stack : prf -> cont -> cont
| co_mut : clos -> cont
with clos:Type :=
| cl : prf -> cont -> clos.


(** Opening up abstractions / mutilde *)

Fixpoint open_rec_prf_prf (k : nat) (p : prf) (q : prf) {struct p} : prf :=
  match p with
    | prf_bvar i    => If k = i then q else (prf_bvar i)
    | prf_fvar a    => prf_fvar a
    | prf_abs p1    => prf_abs (open_rec_prf_prf (S k) p1 q)
    | prf_mu c  => prf_mu (open_rec_clos_prf k c q)
end
with open_rec_cont_prf (k:nat) (e:cont) (q:prf) {struct e} : cont :=
   match e with 
     | co_stack p e => co_stack (open_rec_prf_prf k p q) (open_rec_cont_prf k e q)
     | co_mut c => co_mut (open_rec_clos_prf (S k) c q)
     | co_bvar i=> co_bvar i
     | co_fvar a=> co_fvar a
   end
with open_rec_clos_prf (k:nat) (c:clos) (q:prf) {struct c} : clos :=
   match c with
     | cl p e => cl (open_rec_prf_prf k p q) (open_rec_cont_prf k e q)
   end.

Definition open_prf_prf p q := open_rec_prf_prf 0 p q.
Definition open_cont_prf e q := open_rec_cont_prf 0 e q.
Definition open_clos_prf c q := open_rec_clos_prf 0 c q.
Definition open_prf_prf_var p x := open_rec_prf_prf 0 p (prf_fvar x).
Definition open_cont_prf_var e x := open_rec_cont_prf 0 e (prf_fvar x).
Definition open_clos_prf_var c x := open_rec_clos_prf 0 c (prf_fvar x).


Notation "{ k ~+> q }+ p" := (open_rec_prf_prf k p q) (at level 67).
Notation "{ k ~+> q }- e" := (open_rec_cont_prf k e q) (at level 67).
Notation "{ k ~+> q }* c" := (open_rec_clos_prf k c q) (at level 67).
Notation "p +^^+ q" := (open_prf_prf p q) (at level 67).
Notation "e -^^+ q" := (open_cont_prf e q) (at level 67).
Notation "c *^^+ q" := (open_clos_prf c q) (at level 67).
Notation "p +^+ a" := (open_prf_prf p (prf_fvar a)) (at level 67).
Notation "e -^+ a" := (open_cont_prf e (prf_fvar a)) (at level 67).
Notation "c *^+ a" := (open_clos_prf c (prf_fvar a)) (at level 67).

Lemma open_prf_prf_def p q: p +^^+q = {0 ~+> q}+ p.
Proof. unfolds* open_prf_prf. Qed.
Lemma open_cont_prf_def e q: e -^^+q = {0 ~+> q}- e.
Proof. unfolds* open_cont_prf. Qed.
Lemma open_clos_prf_def c q: c *^^+q= {0 ~+> q}* c.
Proof. unfolds* open_clos_prf. Qed.
Lemma open_prf_prf_var_def p y: p +^+y = {0 ~+> prf_fvar y}+ p.
Proof. unfolds* open_prf_prf. Qed.
Lemma open_cont_prf_var_def e y: e -^+y = {0 ~+> prf_fvar y}- e.
Proof. unfolds* open_cont_prf. Qed.
Lemma open_clos_prf_var_def c y: c *^+y = {0 ~+> prf_fvar y}* c.
Proof. unfolds* open_clos_prf. Qed.
  

(** Opening up mu *)

Fixpoint open_rec_prf_cont (k : nat) (p : prf) (e : cont) {struct p} : prf :=
  match p with
    | prf_bvar i    => prf_bvar i
    | prf_fvar a    => prf_fvar a
    | prf_abs p1    => prf_abs (open_rec_prf_cont (k) p1 e)
    | prf_mu c  => prf_mu (open_rec_clos_cont (S k) c e)
end
with open_rec_cont_cont (k:nat) (e:cont) (f:cont) {struct e} : cont :=
  match e with
     | co_bvar i=> If i=k then f else (co_bvar i)
     | co_fvar a=> co_fvar a
     | co_stack p e' => co_stack (open_rec_prf_cont k p f) (open_rec_cont_cont k e' f)
     | co_mut c => co_mut (open_rec_clos_cont k c f)
   end
with open_rec_clos_cont (k:nat) (c:clos) (f:cont) {struct c} : clos :=
   match c with
     | cl p e => cl (open_rec_prf_cont k p f) (open_rec_cont_cont k e f)
   end.

Definition open_prf_cont p q := open_rec_prf_cont 0 p q.
Definition open_cont_cont e q := open_rec_cont_cont 0 e q.
Definition open_clos_cont c q := open_rec_clos_cont 0 c q.

Notation "{ k ~-> f }+ p" := (open_rec_prf_cont k p f) (at level 67).
Notation "{ k ~-> f }- e" := (open_rec_cont_cont k e f) (at level 67).
Notation "{ k ~-> f }* c" := (open_rec_clos_cont k c f) (at level 67).
Notation "p +^^- f" := (open_prf_cont p f) (at level 67).
Notation "e -^^- f" := (open_cont_cont e f) (at level 67).
Notation "c *^^- f" := (open_clos_cont c f) (at level 67).
Notation "p +^- a" := (open_prf_cont p (co_fvar a)) (at level 67).
Notation "e -^- a" := (open_cont_cont e (co_fvar a)) (at level 67).
Notation "c *^- a" := (open_clos_cont c (co_fvar a)) (at level 67).

Lemma open_prf_cont_def p f: p +^^-f = {0 ~-> f}+ p.
Proof. unfolds* open_prf_cont. Qed.
Lemma open_cont_cont_def e f: e -^^-f = {0 ~-> f}- e.
Proof. unfolds* open_cont_cont. Qed.
Lemma open_clos_cont_def c f: c *^^-f = {0 ~-> f}* c.
Proof. unfolds* open_clos_cont. Qed.
Lemma open_prf_cont_var_def p y: p +^-y = {0 ~-> co_fvar y}+ p.
Proof. unfolds* open_prf_cont. Qed.
Lemma open_cont_cont_var_def e y: e -^-y = {0 ~-> co_fvar y}- e.
Proof. unfolds* open_cont_cont. Qed.
Lemma open_clos_cont_var_def c y: c *^-y = {0 ~-> co_fvar y}* c.
Proof. unfolds* open_clos_cont. Qed.


(** Terms are locally-closed pre-terms *)

Inductive proof : prf -> Prop :=
  | proof_var : forall a,
      proof (prf_fvar a)
  | proof_abs : forall L p,
                  (forall a, a\notin L -> proof (p +^+ a)) ->
                  proof (prf_abs p)
  | proof_mu : forall L c ,
                 (forall a,a\notin L -> closure (c *^- a)) ->
                 proof (prf_mu c)
with context : cont -> Prop :=
     | context_var : forall a, context (co_fvar a)
     | context_stack : forall p e, proof p -> context e -> context (co_stack p e)
     | context_mut : forall L c, (forall a, a\notin L -> closure (c *^+ a)) ->
                     context (co_mut c)
with closure : clos -> Prop :=
     | closure_cl : (forall p e, proof p -> context e -> closure (cl p e))    
.

(** Environment is an associative list mapping variables to types. *)

Definition env := LibEnv.env ltyp.
(********************)
(** Typing relation *)
(********************)

Reserved Notation "E |= p :+ T" (at level 69).
Reserved Notation "E |= e :- T" (at level 69).
Reserved Notation "c :* E" (at level 69).

Inductive typing_prf : env -> prf -> typ -> Prop :=
  | typing_prf_var : forall E a T,
      ok E ->
      binds a (pos T) E ->
      E |= (prf_fvar a) :+ T
  | typing_abs : forall L E U T p1,
      (forall a, a \notin L -> 
        (E & a ~ pos U) |= p1 +^+ a :+ T) ->
      E |= (prf_abs p1) :+ (typ_arrow U T)
  | typing_mu : forall L E T c,
      (forall a, a \notin L ->  
                 c*^-a :* E & a ~ neg T ) ->
      (* Attention ici, on aimerait plutôt a ~ neg T*)
      E |= (prf_mu c) :+ T
with typing_cont : env -> cont -> typ -> Prop :=
  | typing_cont_var : forall E a T,
      ok E ->
      binds a (neg T) E ->
      E |= (co_fvar a) :- (T)
  | typing_mut : forall L E T c,
      (forall a, a \notin L -> 
        c*^+a :* (E & a ~ pos T)) ->
      E |= (co_mut c) :- T
  | typing_stack : forall  E U T q e,
     (E |= q :+ T ) -> 
     ( E |= e :- U ) ->
      E |= (co_stack q e) :- (typ_arrow T U)
with typing_clos : env -> clos -> Prop :=
     | typing_closure : forall E T p e,
        (E |= p :+ T -> E |= e :- T -> (cl p e) :* E)
where "E |= p :+ T" := (typing_prf E p T)
and "E |= e :- T" := (typing_cont E e T)
and "c :* E" := (typing_clos E c)         .


Require Import Coq.Program.Equality.
Scheme typing_prf_ind1 := Induction for typing_prf Sort Prop
with typing_cont_ind1 := Induction for typing_cont Sort Prop
with typing_clos_ind1 := Induction for typing_clos Sort Prop.
(* About typing_clos_ind1. *)

Combined Scheme typing_mut_ind from typing_prf_ind1,typing_cont_ind1,typing_clos_ind1.




(** Definition of values (only abstractions are values) *)

(* FIX ? Rajouter variables ? *)

Inductive value : prf -> Prop :=
  | value_abs : forall p, 
      proof (prf_abs p) -> value (prf_abs p).

(** Reduction relation - one step in call-by-value *)

Inductive red : clos -> clos -> Prop :=
  | red_mut : forall p c,
      context (co_mut c) ->
      value p ->
      red (cl p (co_mut c)) (c*^^+ p)
  | red_abs : forall p q e,
      proof (prf_abs p) -> proof q ->
      context e ->
      red (cl (prf_abs p) (co_stack q e)) (cl q (co_mut (cl p e)))
  | red_mu : forall e c ,
      context e ->
      closure c ->         
      red (cl (prf_mu c) e) (c *^^- e).

Notation "c --> c'" := (red c c') (at level 68).

(** Goal is to prove preservation and progress *)

Definition preservation := forall E c c',
  c :* E ->
  c --> c' ->
   c':* E.

Inductive redn : nat -> clos -> clos -> Prop :=
| red1 : forall c c', red c c' -> redn 1 c c'
| redS : forall c c' n, (exists c'', red c c'' /\ redn n c'' c' ) -> redn (n+1) c c'.

Definition progress := forall p T, 
  empty |= p:+T ->
  value p
  \/ exists p' n, forall a, redn n (cl p (co_fvar a)) (cl p' (co_fvar a)).

