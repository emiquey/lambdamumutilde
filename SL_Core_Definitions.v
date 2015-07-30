(***************************************************************************
* Safety for Lambda Mu Mutilde (CBV) - Infrastructure                      *
* Étienne Miquey, June 2015                                                *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN.
Require Import  L_Core_Definitions 
        L_Core_Infrastructure
        L_Core_Soundness.

 Open Scope list_scope.

(* List Notations *)
Notation  "[ a ]" := (a::nil).
Notation  "[ ]" := (@nil _).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..). 

(*Print typ.
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
*)
(** Grammar of pre-terms. *)

Inductive sprf : Type :=
| sprf_bvar : nat -> sprf (* bound variable in de Bruijn style *)
| sprf_fvar : var -> sprf (* free variable in named style *)
| sprf_abs  : sprf -> sprf
| sprf_mu  :  sclos-> sprf
with scont:Type :=
| sco_bvar: nat -> scont
| sco_fvar: var -> scont
| sco_stack : sprf -> scont -> scont
| sco_mut : sclos -> scont
with store:Type :=
| st : LibEnv.env sprf -> store
with sclos:Type :=
| scl : sprf -> scont -> store -> sclos.


(** Opening up abstractions / mutilde *)

Fixpoint open_rec_sprf_sprf (k : nat) (p : sprf) (q : sprf) {struct p} : sprf :=
  match p with
    | sprf_bvar i    => If k = i then q else (sprf_bvar i)
    | sprf_fvar a    => sprf_fvar a
    | sprf_abs p1    => sprf_abs (open_rec_sprf_sprf (S k) p1 q)
    | sprf_mu c  => sprf_mu (open_rec_sclos_sprf k c q)
end
with open_rec_scont_sprf (k:nat) (e:scont) (q:sprf) {struct e} : scont :=
   match e with 
     | sco_stack p e => sco_stack (open_rec_sprf_sprf k p q) (open_rec_scont_sprf k e q)
     | sco_mut c => sco_mut (open_rec_sclos_sprf (S k) c q)
     | sco_bvar i=> sco_bvar i
     | sco_fvar a=> sco_fvar a
   end
with open_rec_store_sprf (k:nat) (tau:store) (q:sprf) {struct tau}: store :=
   match tau with
     | st l => st (List.map (fun (t:var*sprf) => let (a,p):= t in (a,open_rec_sprf_sprf k p q)) l)
   end
with open_rec_sclos_sprf (k:nat) (c:sclos) (q:sprf) {struct c} : sclos :=
   match c with
     | scl p e tau => scl (open_rec_sprf_sprf k p q) (open_rec_scont_sprf k e q) (open_rec_store_sprf k tau q)
   end.


Definition open_sprf_sprf p q := open_rec_sprf_sprf 0 p q.
Definition open_scont_sprf e q := open_rec_scont_sprf 0 e q.
Definition open_sclos_sprf c q := open_rec_sclos_sprf 0 c q.
Definition open_store_sprf tau q := open_rec_store_sprf 0 tau q.
Definition open_sprf_sprf_var p x := open_rec_sprf_sprf 0 p (sprf_fvar x).
Definition open_scont_sprf_var e x := open_rec_scont_sprf 0 e (sprf_fvar x).
Definition open_sclos_sprf_var c x := open_rec_sclos_sprf 0 c (sprf_fvar x).
Definition open_store_sprf_var tau x := open_rec_store_sprf 0 tau (sprf_fvar x).

Notation "{ k ~+> q }+ p" := (open_rec_sprf_sprf k p q) (at level 67).
Notation "{ k ~+> q }- e" := (open_rec_scont_sprf k e q) (at level 67).
Notation "{ k ~+> q }* c" := (open_rec_sclos_sprf k c q) (at level 67).
Notation "{ k ~+> q } tau" := (open_rec_store_sprf k tau q) (at level 67).
Notation "p +^^+ q" := (open_sprf_sprf p q) (at level 67).
Notation "e -^^+ q" := (open_scont_sprf e q) (at level 67).
Notation "c *^^+ q" := (open_sclos_sprf c q) (at level 67).
Notation "tau ^^+ q" := (open_store_sprf tau q) (at level 67).
Notation "p +^+ a" := (open_sprf_sprf p (sprf_fvar a)) (at level 67).
Notation "e -^+ a" := (open_scont_sprf e (sprf_fvar a)) (at level 67).
Notation "c *^+ a" := (open_sclos_sprf c (sprf_fvar a)) (at level 67).
Notation "tau ^+ a" := (open_store_sprf tau (sprf_fvar a)) (at level 67).

Lemma open_sprf_sprf_def p q: p +^^+q = {0 ~+> q}+ p.
Proof. unfolds* open_sprf_sprf. Qed.
Lemma open_scont_sprf_def e q: e -^^+q = {0 ~+> q}- e.
Proof. unfolds* open_scont_sprf. Qed.
Lemma open_sclos_sprf_def c q: c *^^+q= {0 ~+> q}* c.
Proof. unfolds* open_sclos_sprf. Qed.
Lemma open_store_sprf_def tau q: tau ^^+q= {0 ~+> q} tau.
Proof. unfolds* open_store_sprf. Qed.
Lemma open_sprf_sprf_var_def p y: p +^+y = {0 ~+> sprf_fvar y}+ p.
Proof. unfolds* open_sprf_sprf. Qed.
Lemma open_scont_sprf_var_def e y: e -^+y = {0 ~+> sprf_fvar y}- e.
Proof. unfolds* open_scont_sprf. Qed.
Lemma open_sclos_sprf_var_def c y: c *^+y = {0 ~+> sprf_fvar y}* c.
Proof. unfolds* open_sclos_sprf. Qed.
Lemma open_store_sprf_var_def tau y: tau ^+y = {0 ~+> sprf_fvar y} tau.
Proof. unfolds* open_store_sprf. Qed.
 
(** Opening up mu *)

Fixpoint open_rec_sprf_scont (k : nat) (p : sprf) (e : scont) {struct p} : sprf :=
  match p with
    | sprf_bvar i    => sprf_bvar i
    | sprf_fvar a    => sprf_fvar a
    | sprf_abs p1    => sprf_abs (open_rec_sprf_scont (k) p1 e)
    | sprf_mu c  => sprf_mu (open_rec_sclos_scont (S k) c e)
end
with open_rec_scont_scont (k:nat) (e:scont) (f:scont) {struct e} : scont :=
  match e with
     | sco_bvar i=> If i=k then f else (sco_bvar i)
     | sco_fvar a=> sco_fvar a
     | sco_stack p e' => sco_stack (open_rec_sprf_scont k p f) (open_rec_scont_scont k e' f)
     | sco_mut c => sco_mut (open_rec_sclos_scont k c f)
end
with open_rec_store_scont (k:nat) (tau:store) (f:scont) {struct tau}: store :=
   match tau with
     | st l => st (List.map (fun (t:var*sprf) => let (a,p):=t in (a,open_rec_sprf_scont k p f)) l)
   end
with open_rec_sclos_scont (k:nat) (c:sclos) (f:scont) {struct c} : sclos :=
   match c with
     | scl p e tau=> scl (open_rec_sprf_scont k p f) (open_rec_scont_scont k e f) (open_rec_store_scont k tau f)
   end.


Definition open_sprf_scont p f := open_rec_sprf_scont 0 p f.
Definition open_scont_scont e f := open_rec_scont_scont 0 e f.
Definition open_sclos_scont c f := open_rec_sclos_scont 0 c f.
Definition open_store_scont tau f := open_rec_store_scont 0 tau f.

Notation "{ k ~-> f }+ p" := (open_rec_sprf_scont k p f) (at level 67).
Notation "{ k ~-> f }- e" := (open_rec_scont_scont k e f) (at level 67).
Notation "{ k ~-> f }* c" := (open_rec_sclos_scont k c f) (at level 67).
Notation "{ k ~-> f } tau" := (open_rec_store_scont k tau f) (at level 67).
Notation "p +^^- f" := (open_sprf_scont p f) (at level 67).
Notation "e -^^- f" := (open_scont_scont e f) (at level 67).
Notation "c *^^- f" := (open_sclos_scont c f) (at level 67).
Notation "tau ^^- f" := (open_store_scont tau f) (at level 67).
Notation "p +^- a" := (open_sprf_scont p (sco_fvar a)) (at level 67).
Notation "e -^- a" := (open_scont_scont e (sco_fvar a)) (at level 67).
Notation "c *^- a" := (open_sclos_scont c (sco_fvar a)) (at level 67).
Notation "tau ^- a" := (open_store_scont tau (sco_fvar a)) (at level 67).


Lemma open_sprf_scont_def p f: p +^^-f = {0 ~-> f}+ p.
Proof. unfolds* open_sprf_scont. Qed.
Lemma open_scont_scont_def e f: e -^^-f = {0 ~-> f}- e.
Proof. unfolds* open_scont_scont. Qed.
Lemma open_sclos_scont_def c f: c *^^-f = {0 ~-> f}* c.
Proof. unfolds* open_sclos_scont. Qed.
Lemma open_store_scont_def tau f: tau ^^-f = {0 ~-> f} tau.
Proof. unfolds* open_store_scont. Qed.
Lemma open_sprf_scont_var_def p y: p +^-y = {0 ~-> sco_fvar y}+ p.
Proof. unfolds* open_sprf_scont. Qed.
Lemma open_scont_scont_var_def e y: e -^-y = {0 ~-> sco_fvar y}- e.
Proof. unfolds* open_scont_scont. Qed.
Lemma open_sclos_scont_var_def c y: c *^-y = {0 ~-> sco_fvar y}* c.
Proof. unfolds* open_sclos_scont. Qed.
Lemma open_store_scont_var_def tau y: tau ^-y = {0 ~-> sco_fvar y} tau.
Proof. unfolds* open_store_scont. Qed.


(** Substitution for names *)

(* substitute z in p by q *)


(*Definition subst_prf_store (a:var) (p:sprf)

Fixpoint subst_store (c:sclos) {struct c} : clos :=
  match c with
    |scl p e (st l) =>
     match l with
         | nil  => cl (prf_abs (prf_bvar 0)) (co_bvar 0)
         | h::q => cl (prf_abs (prf_bvar 0)) (co_mut (subst_store (scl p e (st q))))
     end
  end
.
*)

     

Fixpoint subst_sprf_sprf (z : var) (p: sprf) (q : sprf) {struct p} : sprf :=
  match p with
  | sprf_bvar i    => sprf_bvar i
  | sprf_fvar x    => If x = z then q else (sprf_fvar x)
  | sprf_abs p1    => sprf_abs (subst_sprf_sprf z p1 q)
  | sprf_mu c => sprf_mu (subst_sclos_sprf z c q) 
end
with subst_scont_sprf (z : var) (e:scont) (q:sprf) {struct e}:scont :=
  match e with
    | sco_bvar i => sco_bvar i
    | sco_fvar x => sco_fvar x
    | sco_stack p f => sco_stack (subst_sprf_sprf z p q) (subst_scont_sprf z f q)
    | sco_mut c => sco_mut (subst_sclos_sprf z c q)
  end
with subst_store_sprf (z:var) (tau:store) (q:sprf) {struct tau} : store :=
  match tau with
    | st l  => st (List.map (fun (t:var*sprf) =>let (a,p):=t in (a,(subst_sprf_sprf z p q))) l)
  end
with subst_sclos_sprf (z:var) (c:sclos) (q:sprf) {struct c} : sclos :=
  match c with
    | scl p e tau =>  scl (subst_sprf_sprf z p q)  (subst_scont_sprf z e q) (subst_store_sprf z tau q)
  end.


Fixpoint subst_sprf_scont (z : var) (p: sprf) (f:scont) {struct p} : sprf :=
  match p with
  | sprf_bvar i    => sprf_bvar i
  | sprf_fvar x    => sprf_fvar x
  | sprf_abs p1    => sprf_abs (subst_sprf_scont z p1 f)
  | sprf_mu c => sprf_mu (subst_sclos_scont z c f) 
end
with subst_scont_scont (z : var) (e:scont) (f:scont) {struct e}:scont :=
  match e with
    | sco_bvar i => sco_bvar i
    | sco_fvar x => If x = z then f else sco_fvar x
    | sco_stack p e' => sco_stack (subst_sprf_scont z p f) (subst_scont_scont z e' f)
    | sco_mut c => sco_mut (subst_sclos_scont z c f)
  end
with subst_store_scont (z:var) (tau:store) (f:scont) {struct tau} : store :=
  match tau with
    | st l  => st (List.map (fun (t:var*sprf) =>let (a,p):=t in (a,(subst_sprf_scont z p f))) l)
  end
with subst_sclos_scont (z:var) (c:sclos) (f:scont) {struct c} : sclos :=
  match c with
    | scl p e tau =>  scl (subst_sprf_scont z p f)  (subst_scont_scont z e f) (subst_store_scont z tau f)
  end.

Notation "[ z ~+> q ]+ p" := (subst_sprf_sprf z p q) (at level 68).
Notation "[ z ~+> q ]- e" := (subst_scont_sprf z e q) (at level 68).
Notation "[ z ~+> q ]* c" := (subst_sclos_sprf z c q) (at level 68).
Notation "[ z ~+> q ] tau":= (subst_store_sprf z tau q) (at level 68).
Notation "[ z ~-> f ]+ p" := (subst_sprf_scont z p f) (at level 68).
Notation "[ z ~-> f ]- e" := (subst_scont_scont z e f) (at level 68).
Notation "[ z ~-> f ]* c" := (subst_sclos_scont z c f) (at level 68).
Notation "[ z ~-> f ] tau":= (subst_store_scont z tau f) (at level 68).


Fixpoint subst_list_in_sprf (p:sprf) (l:list (var*sprf)) {struct l}: sprf:=
  match l with
    |nil => p
    |cons (a,q) t => subst_list_in_sprf (subst_sprf_sprf a p q) t
  end.

Definition subst_store_in_sprf (p:sprf) (tau:store):sprf :=
  match tau with
    |st l => subst_list_in_sprf p l
  end.

Fixpoint subst_list_in_scont (e:scont) (l:list (var*sprf)) {struct l}: scont:=
  match l with
    |nil => e
    |cons (a,q) t => subst_list_in_scont (subst_scont_sprf a e q) t
  end.

Definition subst_store_in_scont (e:scont) (tau:store):scont :=
  match tau with
    |st l => subst_list_in_scont e l
  end.


(** Terms are locally-closed pre-terms *)

Inductive in_list {A:Type}: A -> list A-> Prop :=
|in_member : forall a l, in_list a (a::l)
|in_cons : forall a l, (forall b, in_list a l -> in_list a (b::l)).
  

Inductive sproof : sprf -> Prop :=
  | proof_var : forall a,
                  sproof (sprf_fvar a)
  | proof_abs : forall L p,
                  (forall a, a\notin L -> sproof (p +^+ a)) ->
                  sproof (sprf_abs p)
  | proof_mu : forall L c ,
                 (forall a,a\notin L -> sclosure (c *^- a)) ->
                 sproof (sprf_mu c)
with scontext : scont -> Prop :=
     | scontext_var : forall a, scontext (sco_fvar a)
     | scontext_stack : forall p e, sproof p -> scontext e -> scontext (sco_stack p e)
     | scontext_mut : forall L c, (forall a, a\notin L -> sclosure (c *^+ a)) ->
                                 scontext (sco_mut c)
with store_ok : store -> Prop :=
     | store_st : forall l, (forall a p, (in_list (a,p) l) -> sproof p) -> store_ok (st l)
with sclosure : sclos -> Prop :=
     | sclosure_cl : (forall p e tau, sproof p -> scontext e -> store_ok tau -> sclosure (scl p e tau))    
.

(** Environment is an associative list mapping variables to types. *)

Definition env := LibEnv.env ltyp.

(********************)
(** Typing relation *)
(********************)

(* Reserved Notation "E|tau |= p :+ T" (at level 69).
Reserved Notation "E|tau |= e :- T" (at level 69).
Reserved Notation "c|tau :* E" (at level 69).
 *)

Definition concat_env tau tau' :=
  match (tau,tau') with
    |(st l,st l') => st (concat l l')
  end.

Notation "tau @@ tau'" := (concat_env tau tau') (at level 67).

Definition cons_env a p tau :=
  match tau with
    |st l => st (cons (a,p) l )
  end.


Inductive typing_sprf : env -> store -> sprf -> typ -> Prop :=
  | typing_sprf_var : forall E tau a T,
      ok E ->
      binds a (pos T) E ->
      typing_sprf E tau (sprf_fvar a)  T
  |typing_store_var : forall E tau a T,
                        (exists (q:sprf) l, tau=st l /\ binds a q l /\ typing_sprf E (st l) q T)->
                        typing_sprf E tau (sprf_fvar a) T
  | typing_abs : forall L E tau U T p1,
      (forall a, (a \notin L) -> 
        typing_sprf (E & a ~pos U) tau (p1 +^+ a)  T) ->
     typing_sprf E tau (sprf_abs p1) (typ_arrow U T)

  | typing_mu : forall L E tau T c,
      (forall a, a \notin L ->  
                 typing_sclos (E & a ~ neg T) tau (c*^-a))  ->
      typing_sprf  E tau (sprf_mu c) T
with typing_scont : env -> store -> scont -> typ -> Prop :=
  | typing_cont_var : forall E tau a T,
      ok E ->
      binds a (neg T) E ->
      typing_scont E tau (sco_fvar a) (T)
  | typing_mut : forall L E tau T c,
      (forall a, a \notin L -> 
        typing_sclos (E & a ~ pos T) tau (c*^+a)) ->
      typing_scont E tau  (sco_mut c)  T
  | typing_stack : forall  E tau U T q e,
     (typing_sprf E tau q T) -> 
     (typing_scont E tau e U) ->
      typing_scont E tau (sco_stack q e) (typ_arrow T U)
with typing_sclos : env -> store -> sclos -> Prop :=
  | typing_sclosure : forall E tau tau' T p e,
     (typing_sprf E (tau'@@tau) p T ->
      typing_scont E (tau'@@tau) e T ->
      typing_sclos E tau (scl p e tau')).


Notation "E ; tau |= p :+ T" := (typing_prf E tau p T) (at level 68).
Notation "E ; tau |= e :- T" := (typing_scont E tau e T) (at level 68).
Notation "c :* E ; tau " := (typing_sclos E tau c ) (at level 68).


(*** NOTATIONS ??? ****) 


Require Import Coq.Program.Equality.
Scheme typing_sprf_ind1 := Induction for typing_sprf Sort Prop
with typing_scont_ind1 := Induction for typing_scont Sort Prop
with typing_sclos_ind1 := Induction for typing_sclos Sort Prop.
(* About typing_sclos_ind1. *)

Combined Scheme typing_store_mut_ind from typing_sprf_ind1,typing_scont_ind1,typing_sclos_ind1.


(** Definition of values (only abstractions are values) *)

(* FIX ? Rajouter variables ? *)

Inductive value : sprf -> Prop :=
  | value_abs : forall p, 
      sproof (sprf_abs p) -> value (sprf_abs p).

(** Reduction relation - one step in call-by-value *)

Definition sclos_concat_store (c:sclos) (tau:store): sclos :=
  match c with
    | scl p e tau' => scl p e (concat_env tau tau')
  end.

Definition sclos_append_store (c:sclos) (tau:store): sclos :=
  match c with
    | scl p e tau' => scl p e (concat_env tau' tau)
  end.

Definition void:store := st nil.

Inductive sred : sclos -> sclos -> Prop :=
  | sred_mut : forall p c tau,
      scontext (sco_mut c) ->
      value p -> forall L a, (a \notin L -> 
      sred (scl p (sco_mut c) tau) (sclos_append_store (c*^+ a) (cons_env a p tau)))
  | sred_abs : forall p q e tau,
      sproof (sprf_abs p) -> sproof q ->
      scontext e ->
      sred (scl (sprf_abs p) (sco_stack q e) tau) (scl q (sco_mut (scl p e void)) tau)
  | sred_mu : forall e c tau,
      sproof (sprf_mu c) -> scontext e ->
      sred (scl (sprf_mu c) e tau) (sclos_append_store (c *^^- e) tau).

Notation "c -s-> c'" := (sred c c') (at level 68).

(** Goal is to prove preservation and progress *)

Definition preservation := forall E c c',
  typing_sclos E void c ->
  c -s-> c' ->
  typing_sclos E void c'.


Definition progress := forall p T, 
  typing_sprf empty void p T ->
  value p
  \/ (exists L, forall a,(a\notin L -> exists c, sred (scl p (sco_fvar a) void) c)).

