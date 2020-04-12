(*! Definition of a total map using a partial map !*)

Require Import PresburgerAI.PartialMap.
Require Import EquivDec.

Module TotalMap.

  Section Methods.

        (** Definition of a total map defined by a partial map and a default value **)
    Record TotalMap {Key} {Value} :=
      mk {
          partial_map : PartialMap Key Value;
          default : Value
        }.

    Global Arguments TotalMap : clear implicits.

    Context {Key: Type}
            {Value: Type}
            {EqKey: EqDec Key eq}.

    (** An empty total map **)
    Definition empty (default: Value) :=
      mk Key Value PartialMap.empty default.

    (** Get the value of a key **)
    Definition get (m: TotalMap Key Value) (k: Key) :=
      match (PartialMap.get (partial_map m) k) with
      | Some v => v
      | None => default m
      end.

    (** Remove a key **)
    Definition remove (m: TotalMap Key Value) (k: Key) :=
      mk _ _ (PartialMap.remove (partial_map m) k) (default m).

    (** Set the value of a key **)
    Definition put (m: TotalMap Key Value) (k: Key) (v: Value) :=
      mk _ _ (PartialMap.put (partial_map m) k v) (default m).

  End Methods.

End TotalMap.

(** Notation for an empty map with a default value **)
Notation "'_' '!!->' v" :=
  (TotalMap.empty v) (at level 100).

(** Notation for a map update **)
Notation "k '!!->' v ';' m" :=
  (TotalMap.put m k v) (at level 100, v at next level, right associativity).

(** Notation for a map remove **)
Notation "k '!!->' '_' ';' m" :=
  (TotalMap.remove m k) (at level 100, right associativity).

Notation TotalMap := TotalMap.TotalMap.
