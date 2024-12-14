
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope string_scope.
Require Import Coq.Arith.PeanoNat.

Require Export MST.Digraphs.
Require Export MST.Graphs.

(* Playing aroudn with Graphs for our reference -- disregard this section *)
Definition vertex0 := index 0. 
Definition vertex1 := index 1. 
Definition vertex2 := index 2. 

Definition arc0 := (A_ends vertex0 vertex1). 
Definition arc1 := (A_ends vertex1 vertex2). 

Definition set_of_vertices0 := (V_union (V_single vertex0) V_empty).
Definition set_of_vertices1 := (V_union (V_single vertex1) set_of_vertices0).
Definition set_of_vertices2 := (V_union (V_single vertex2) set_of_vertices1).

Definition set_of_vertices_final := (V_union (V_single vertex2) (V_union (V_single vertex1) (V_union (V_single vertex0) V_empty))).

Definition set_of_arcs0 := (A_union (A_single arc0) A_empty). 
Definition set_of_arcs1 := (A_union (A_single arc1) set_of_arcs0).

Definition set_of_arcs_final := (A_union (A_single arc1) (A_union (A_single arc0) A_empty)).

Definition graph_constructed := Graph set_of_vertices_final set_of_arcs_final. 

Check set_of_vertices_final. 
Check set_of_arcs_final. 
Check graph_constructed. 

Definition empty_graph : Graph V_empty A_empty := G_empty.
Definition graph_v0 := G_vertex V_empty A_empty G_empty vertex0 (fun H => match H with end).

(* Testing the imported list and string packages *)
Compute ("a" ++ "b")%string. 
Compute ([1] ++ [2]). 

(* Actual Code for displaying graphs in QuickChick *)
Class Show A : Type :=
{
  show : A -> string
}.

(* Retrieved from the Typeclasses chapter of Software Foundations Volume 4: QuickChick *)
Fixpoint string_of_nat_aux (time n : nat) (acc : string) : string :=
  let d := match n mod 10 with
           | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
           | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
           end in
  let acc' := (d ++ acc)%string in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => string_of_nat_aux time' n' acc'
      end
  end.

Definition string_of_nat (n : nat) : string := string_of_nat_aux n n "".

#[export] Instance showNat : Show nat :=
{
    show := string_of_nat
}.

(* Retrieved from the Typeclasses chapter of Software Foundations Volume 4: QuickChick *)
Fixpoint showListAux {A : Type} (s : A -> string) (l : list A) : string :=
  match l with
    | nil => ""
    | cons h nil => s h
    | cons h t => append (append (s h) ", ") (showListAux s t)
  end.
#[export] Instance showList {A : Type} `{Show A} : Show (list A) :=
{
  show l := append "[" (append (showListAux show l) "]")
}.

#[export] Instance Show_Vertex : Show Vertex := 
{
  show := 
    fun vertex => 
      match vertex with
        | index x => ("Vertex " ++ (show x))%string
      end
}.

#[export] Instance Show_Arc: Show Arc :=
{
  show :=
    fun arc => 
      match arc with 
        | A_ends x y => (((("(" ++ (show x))%string ++ ", ")%string ++ (show y))%string ++ ")")%string
      end 
}.

(* Simple Sanity Checks *)
Compute (show vertex0). 
Definition listy1 := [vertex0; vertex1]. 
Compute (show listy1). 

Compute (show arc0). 
Definition listy2 := [arc0; arc1]. 
Compute (show listy2). 

#[export] Instance Show_Graph {v : V_set} {a: A_set} : Show (Graph v a) :=
{
  show := fun g =>
    let vertices := GV_list v a g in
    let edges := GA_list v a g in
    ("Vertices: " ++ show vertices ++ ", Edges: " ++ show edges)%string
}.

(* Simple Sanity Check *)
Check graph_v0. 
Compute (show graph_v0). 

(* Generator Code is buggy and doesn't work, hence nothing is included down below *)










