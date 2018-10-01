Require Import List.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.ListMonad.
From QuickChick Require Import
     GenLowInterface RandomQC RoseTrees Sets Tactics.

Import MonadNotation.
Import ApplicativeNotation.
Local Open Scope monad_scope.
Local Open Scope list_scope.


Inductive LazyList (A : Type) : Type :=
| lnil : LazyList A
| lcons : A -> Lazy (LazyList A) -> LazyList A.

Definition tl `{A : Type} (l : LazyList A) : LazyList A :=
  match l with
  | lnil => lnil _
  | lcons x l' => force l'
  end.


Fixpoint lazy_append {A : Type} (l1 : LazyList A) (l2 : LazyList A) : LazyList A :=
  match l1 with
  | lnil => l2
  | lcons x l1' => lcons _ x (lazy (lazy_append (force l1') l2))
  end.

(* Functor instace for LazyList *)
Fixpoint mapLazyList {A B : Type} (f : A -> B) (l : LazyList A) : LazyList B :=
  match l with
  | lnil => lnil _
  | lcons x l' => lcons _ (f x) (lazy (mapLazyList f (force l')))
  end.

Instance FunctorLazyList : Functor LazyList :=
  {
    fmap := @mapLazyList
  }.


Fixpoint lazyTake {A : Type} (n : nat) (l : LazyList A) : List.list A :=
  match n with
  | O => nil
  | S n' => match l with
           | lnil => nil
           | lcons x l' => x :: lazyTake n' (force l')
           end
  end.

Fixpoint LazyList_to_list {A : Type} (l : LazyList A) : list A :=
  match l with
  | lnil => nil
  | lcons x l' => cons x (LazyList_to_list (force l'))
  end.


(* Monad instance for LazyList *)
Definition retLazyList {A : Type} (a : A) : LazyList A :=
  lcons _ a (lazy (lnil _)).

Fixpoint concatLazyList {A : Type} (l : LazyList (LazyList A)) : LazyList A :=
  match l with
  | lnil => lnil _
  | lcons x l' => lazy_append x (concatLazyList (force l'))
  end.

Definition bindLazyList {A B : Type} (l : LazyList A) (f : A -> LazyList B) : LazyList B :=
  concatLazyList (mapLazyList f l).

Instance MonadLazyList : Monad LazyList :=
  {
    ret := @retLazyList;
    bind := @bindLazyList
  }.

(* Guard definition, because ExtLib doesn't have Alternative *)
Definition guard (b : bool) : LazyList unit :=
  match b with
  | true => ret tt
  | false => lnil _
  end.

(* A "Series A" is a function that takes a depth, and produces a list
   of all "A"s up to that depth *)
Definition Series A := nat -> LazyList A.


(* Serial typeclass, types that we can enumerate all values of up to a certain depth. *)
Class Serial (A : Type) : Type :=
  {
    series : Series A
  }.


(* Union of two series *)
Definition series_sum {A : Type} (s1 s2 : Series A) : Series A
  := fun d => lazy_append (s1 d) (s2 d).


(* Product of two series *)
Definition series_prod {A B : Type} (s1 : Series A) (s2 : Series B) : Series (A * B)
  := fun d => x <- s1 d;;
             y <- s2 d;;
             ret (x, y).


(* Functor instace for Series *)
Definition mapSeries {A B : Type} (f : A -> B) (sa : Series A) : Series B :=
  fun n => let a := sa n in
        mapLazyList f a.

Instance FunctorSeries : Functor Series :=
  {
    fmap := @mapSeries
  }.

Definition mapSerial {A B : Type} (f : A -> B) (sa : Serial A) : Serial B :=
  Build_Serial _ (mapSeries f (@series A sa)).

Instance FunctorSerial : Functor Serial :=
  {
    fmap := @mapSerial
  }.


(* Applicative instance for series *)
Definition pureSeries {A : Type} (a : A) : Series A :=
  fun n => retLazyList a.

Definition apSeries {A B : Type} (sab : Series (A -> B)) (sa : Series A) : Series B :=
  fun n => let list_of_f := sab n in
        let list_of_a := sa n in
        list_of_f <*> list_of_a.

Instance ApplicativeSeries : Applicative Series :=
  {
    pure := @pureSeries;
    ap := @apSeries
  }.


(* Monad instance for series *)
Definition retSeries {A : Type} (a : A) : Series A :=
  fun n => retLazyList a.

Definition bindSeries {A B : Type} (sa : Series A) (f : A -> Series B) : Series B :=
  fun n => let list_of_a := sa n in
        let list_of_sb := fmap f list_of_a in
        sbs <- list_of_sb ;;
            sbs n.

Instance monadSeries : Monad Series :=
  {
    bind := @bindSeries;
    ret := @retSeries
  }.


Definition retSerial {A : Type} (a : A) : Serial A :=
  Build_Serial _ (retSeries a).

Definition bindSerial {A B : Type} (sa : Serial A) (f : A -> Serial B) : Serial B :=
  Build_Serial _ (bindSeries series (fun x => @series _ (f x))).

Instance monadSerial : Monad Serial :=
  {
    bind := @bindSerial;
    ret := @retSerial
  }.

Definition smoosh `{A : Type} (n : nat) (l : Lazy (list (Serial (Rose A)))) : Lazy (list (Rose A)) :=
  lazy (s <- force l;;
        LazyList_to_list (@series _ s n)).


Fixpoint promote {A : Type} (n : nat) (m : Rose (Serial A)) : Serial (Rose A) :=
  match m with
  | MkRose h ts => fmap (fun h => MkRose h (smoosh n (lazy (map (promote (n-1)) (force ts))))) h
  end.

Definition semGenSize {A : Type} (g : Serial A) (s : nat) : set A := list_In (LazyList_to_list (@series _ g s)).
Definition semGen {A : Type} (g : Serial A) : set A := \bigcup_s semGenSize g s.

  (* More things *)
(*
  Definition bindGen_aux {A : Type} (g : Serial A) (n : nat) (r : RandomSeed) : semGen g (@series _ g n).
    unfold semGen, semGenSize, codom, bigcup.
    exists n; split => //=.
    exists r; auto.
  Qed.
*)

(*
  Definition bindGen' {A B : Type} (g : Serial A) (k : forall (a : A), (a \in semGen g) -> Serial B) : Serial B :=
    Build_Serial (fun n r =>
                    let (r1,r2) := randomSplit r in
                    run (k (run g n r1) (bindGen_aux g n r1)) n r2).
*)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool ssrnat eqtype seq.

Fixpoint foldSerial {A B : Type} (f : A -> B -> Serial A) (l : list B) (a : A)
: Serial A := nosimpl(
  match l with
    | nil => ret a
    | (x :: xs) => bind (f a x) (foldSerial f xs)
  end).

Definition liftSerial {A B} (f: A -> B) (a : Serial A)
: Serial B := nosimpl
             (bind a (fun x =>
              ret (f x))).


(* Helper functions for generating Series's for constructors of "n" arguments *)
Definition cons0 {A} (con : A) : Series A := fun d => ret con.
Definition cons1 {A B} `{Serial A} (con : A -> B) : Series B
  := fun d => guard (Nat.ltb 0 d);;
            a <- series (d-1);;
            ret (con a).
Definition cons2 {A B C} `{Serial A} `{Serial B} (con : A -> B -> C) : Series C
  := fun d => guard (Nat.ltb 0 d);;
            p <- series_prod series series (d-1) ;;
            match p with
            | (a, b) => ret (con a b)
            end.
Definition cons3 {A B C D} `{Serial A} `{Serial B} `{Serial C} (con : A -> B -> C -> D) : Series D
  := fun d => guard (Nat.ltb 0 d);;
            p <- series_prod series (series_prod series series) (d-1) ;;
            match p with
            | (a, (b, c)) => ret (con a b c)
            end.


(* Explicit cons variants for defining typeclass instances... *)
Definition expcons0 {A} (con : A) : Series A := fun d => ret con.
Definition expcons1 {A B} (sa : Series A) (con : A -> B) : Series B
  := fun d => match d with
           | 0 => lnil _
           | S d' => a <- sa d';;
                      ret (con a)
           end.
Definition expcons2 {A B C} (sa : Series A) (sb : Series B) (con : A -> B -> C) : Series C
  := fun d => match d with
           | 0 => lnil _
           | S d' => p <- series_prod sa sb d' ;;
                      match p with
                      | (a, b) => ret (con a b)
                      end
           end.
Definition expcons3 {A B C D} (sa : Series A) (sb : Series B) (sc : Series C) (con : A -> B -> C -> D) : Series D  := fun d => match d with
           | 0 => lnil _
           | S d' => p <- series_prod sa (series_prod sb sc) d' ;;
                      match p with
                      | (a, (b, c)) => ret (con a b c)
                      end
           end.


Fixpoint series_nat (n : nat) : LazyList nat :=
  series_sum (expcons0 0) (expcons1 series_nat S) n.

Instance nat_serial : Serial nat :=
  {
    series := series_nat
  }.



Fixpoint series_list {A : Type} `{Serial A} (n : nat) : LazyList (list A) :=
  series_sum (expcons0 nil) (expcons2 series series_list cons) n.

Instance list_serial {A : Type} `{Serial A} : Serial (list A) :=
  {
    series := series_list
  }.
