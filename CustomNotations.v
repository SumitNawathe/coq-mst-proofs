Require Export MST.Sets.
Require Export MST.Vertices.
Require Export MST.Edges.

Declare Scope uset_scope.
Open Scope uset_scope.
Delimit Scope uset_scope with U_set.
Bind Scope uset_scope with U_set.

Notation "A '⊆' B" := (Included _ A B)
	(at level 75) : uset_scope.
Notation "A '⊄' B" := (~ (Included _ A B))
	(at level 75) : uset_scope.
Notation "∅" := (Empty _)
	(at level 50) : uset_scope.
Notation "A '\' B" := (Differ _ A B)
	(at level 70) : uset_scope.
Notation "'⟨' x '⟩'" := (Single _ x)
	(at level 0, x at level 99) : uset_scope.
Notation "x ∈ A" := ((A: U_set _) x)
	(at level 65) : uset_scope.
Notation "x ∉ A" := (~ (A: U_set _) x)
	(at level 65) : uset_scope.
Notation "A ∪ B" := (Union _ A B)
	(at level 65) : uset_scope.
Notation "A ∩ B" := (Inter _ A B)
	(at level 65) : uset_scope.
Notation "x '--' y" := (A_ends x y)
	(at level 65) : uset_scope.
Notation "x '~~' y" := (E_ends x y)
	(at level 65) : uset_scope.

