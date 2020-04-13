(*! Definition of a partial map using lists !*)

Require Import List.
Require Export PresburgerAI.EqDec.

Module PartialMap.

  Section Methods.

    (** Definition of a partial map defined by a list of (Key, Value) pairs **)
    Definition PartialMap Key Value {EqKey: EqDec Key eq} := list (Key * Value).

    Context {Key: Type}
            {Value: Type}
            {EqKey: EqDec Key eq}.

    (** An empty partial map **)
    Definition empty : PartialMap Key Value := nil.

    (** Get the value of a key **)
    Definition get (m: PartialMap Key Value) (k: Key) :=
      let pair := find (fun '(k', v) => k == k') m in
      option_map (fun '(key, val) => val) pair.

    (** Remove a key **)
    Definition remove (m: PartialMap Key Value) (k: Key) :=
      filter (fun '(k', v) => k == k') m.

    (** Set the value of a key **)
    Definition put (m: PartialMap Key Value) (k: Key) (v: Value) :=
      (k, v)::(remove m k).

  End Methods.

End PartialMap.

(** Notation for an map with a single value **)
Notation "k '!->' v" :=
  (PartialMap.put PartialMap.empty k v) (at level 100).

(** Notation for a map update **)
Notation "k '!->' v ';' m" :=
  (PartialMap.put m k v) (at level 100, v at next level, right associativity).

(** Notation for a map remove **)
Notation "k '!->' '_' ';' m" :=
  (PartialMap.remove m k) (at level 100, right associativity).

Coercion PartialMap.get : PartialMap.PartialMap >-> Funclass.

Notation PartialMap := PartialMap.PartialMap.
