import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionBundleRaw

/-! Exact assignment semantics of the literal fixed-list product writer.
No oracle equality, gadget realization or reduction is supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionBundleValue
open Computability Holant Holant.Tractable Holant.Complexity
open scoped BigOperators
namespace F
export GeneralEOPairedCSPFamilyRaw (Raw)
end F
namespace R
export GeneralEOPairedCSPRaw (Raw read)
end R
namespace B
export GeneralEOPairedFamilyExtractionBundleRaw (append query query_variables query_valid)
end B
namespace V
export GeneralEOPairedFamilyExtractionRestrictionValue (query query_valid minor addresses_at anchor_port)
end V
namespace T
export GeneralEOPairedFamilyExtractionWriter (weight weight_cons weight_nil weight_labels rawValue)
end T
namespace Pn
export GeneralEOPairedFamilyExtractionPinRaw (weight anchor fixed free)
end Pn
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {s : ℕ} {arity : ℕ → ℕ} (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))
variable {K : Type*} [CommSemiring K] (g : (i : Fin s) → Signature K (P i).count)

theorem weight_congr (ls : List (Fin s)) (a b : ℕ → Bool)
    (h : ∀k,k<(ls.map (fun i => (P i).count)).sum → a k=b k) :
    T.weight P g ls a=T.weight P g ls b := by
  induction ls generalizing a b with
  | nil => rfl
  | cons i ls ih =>
    rw [T.weight_cons,T.weight_cons]
    congr 1
    · congr 1
      funext j
      exact h j.val (by simp only [List.map_cons,List.sum_cons]; omega)
    · apply ih
      intro k hk
      exact h ((P i).count+k) (by simpa only [List.map_cons,List.sum_cons] using Nat.add_lt_add_left hk (P i).count)

theorem weight_append (ls rs : List (Fin s)) (a : ℕ → Bool) :
    T.weight P g (ls++rs) a=T.weight P g ls a*
      T.weight P g rs (fun k => a ((ls.map (fun i => (P i).count)).sum+k)) := by
  induction ls generalizing a with
  | nil => simp
  | cons i ls ih =>
    simp only [List.cons_append,T.weight_cons,ih,List.map_cons,List.sum_cons,mul_assoc,Nat.add_assoc]

theorem append_weight (r t : F.Raw s)
    (hr : r.addresses.length=r.edgeCount P) (a : ℕ → Bool) :
    Pn.weight P g (B.append r t) a=Pn.weight P g r a*Pn.weight P g t a := by
  change r.addresses.length=(r.labels.map (fun i => (P i).count)).sum at hr
  unfold Pn.weight B.append
  dsimp only
  rw [weight_append]
  congr 1
  · apply weight_congr
    intro k hk
    rw [List.getD_append _ _ _ _ (by simpa only [hr,GeneralEOPairedCSPFamilyRaw.Raw.edgeCount] using hk)]
  · apply weight_congr
    intro k hk
    rw [←hr,List.getD_append_right _ _ _ _ (Nat.le_add_right _ _),Nat.add_sub_cancel_left]

variable {m : ℕ} (left right : Fin s)
variable (p : Fin ((P left).count+(P right).count) → Bool ⊕ Fin m)

theorem minor_weight (r : R.Raw) (x : Fin r.variables → Bool) :
    Pn.weight P g (V.query P left right p r) (Pn.anchor false true x)=
      ∏v : Fin r.constraints,V.minor P left right p g
        (fun j => R.read x (r.addresses.getD (v.val*m+j.val) 0)) := by
  change T.weight P g (GeneralEOPairedFamilyExtractionWriter.labels left right r.constraints)
    (fun k => Pn.anchor false true x ((GeneralEOPairedFamilyExtractionRestrictionRaw.addresses p r).getD k 0))=_
  rw [T.weight_labels]
  apply Finset.prod_congr rfl
  intro v _
  congr 1
  funext j
  rw [V.addresses_at,V.anchor_port]
  rfl

variable (ps : List (Fin ((P left).count+(P right).count) → Bool ⊕ Fin m))

def coefficient : Signature K m := fun z => (ps.map (fun p => V.minor P left right p g z)).prod

theorem query_weight (r : R.Raw) (hr : r.WellFormed m) (x : Fin r.variables → Bool) :
    Pn.weight P g (B.query P left right ps r) (Pn.anchor false true x)=
      ∏v : Fin r.constraints,coefficient P g left right ps
        (fun j => R.read x (r.addresses.getD (v.val*m+j.val) 0)) := by
  induction ps with
  | nil => simp [B.query,Pn.weight,coefficient]
  | cons p ps ih =>
    rw [B.query,append_weight P g (V.query P left right p r) (B.query P left right ps r)
      (by exact (V.query_valid P left right p r hr).1),
      minor_weight,ih]
    simp only [coefficient,List.map_cons,List.prod_cons,Finset.prod_mul_distrib]

theorem query_value (r : R.Raw) (hr : r.WellFormed m) :
    Pn.fixed P g (B.query P left right ps r) false true=
      T.rawValue (coefficient P g left right ps) r := by
  cases ps with
  | nil =>
    unfold Pn.fixed T.rawValue
    apply Finset.sum_congr rfl
    intro x _
    exact query_weight P g left right [] r hr x
  | cons p ps =>
    unfold Pn.fixed T.rawValue
    apply Finset.sum_congr rfl
    intro x _
    exact query_weight P g left right (p::ps) r hr x


end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionBundleValue
