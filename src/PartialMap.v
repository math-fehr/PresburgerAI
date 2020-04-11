(*! Definition of a partial map using lists !*)

Require Import List EquivDec.

Module PartialMap.

  Section Methods.

    (** Definition of a partial map defined by a list of (Key, Value) pairs **)
    Definition PartialMap Key Value := list (Key * Value).

    Context {Key: Type}
            {Value: Type}
            {EqKey: EqDec Key eq}.

    (** An empty partial map **)
    Definition empty : PartialMap Key Value := nil.

    (** Get the value of a key **)
    Definition get (m: PartialMap Key Value) (k: Key) :=
      let pair := find (fun '(k', v) => if equiv_dec k k' then true else false) m in
      option_map (fun '(key, val) => val) pair.

    (** Remove a key **)
    Definition remove (m: PartialMap Key Value) (k: Key) :=
      filter (fun '(k', v) => if equiv_dec k k' then false else true) m.

    (** Set the value of a key **)
    Definition put (m: PartialMap Key Value) (k: Key) (v: Value) :=
      (k, v)::(remove m k).

  End Methods.

End PartialMap.

(** Notation for an empty map **)
Notation "k '!->' v" :=
  (PartialMap.put PartialMap.empty k v) (at level 100).

(** Notation for a map update **)
Notation "k '!->' v ';' m" :=
  (PartialMap.put m k v) (at level 100, v at next level, right associativity).

(** Notation for a map remove **)
Notation "k '!->' '_' ';' m" :=
  (PartialMap.remove m k) (at level 100, right associativity).

