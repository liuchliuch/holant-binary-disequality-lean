import Holant.Proofs.Hardness.GeneralEONegativeSupportClosure
import Holant.Proofs.Hardness.EONegativeWitness
import Holant.Proofs.Hardness.EOBinaryPlaneTract

/-! Arbitrary-arity pairing producer on ternary-XOR-closed EO support.
The selected pairing covers the ENTIRE original support. Consequently the
full paired lift is exactly the original signature, with every coefficient
unchanged, and a failed all-pairings class condition fails at this pairing.
This supplies the local compatibility condition needed by occurrence-cycle
CSP graph compilation; no pairing restriction oracle is presumed available. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeClosedSupport
open Holant Holant.Tractable
namespace PC
export Holant.LocalDrafts.Tractability.EOEvaluation.PairingConstruction (pairing covers twice_count)
end PC
namespace D
export Holant.LocalDrafts.Tractability.EOEvaluation.PairingCharacters (Data)
end D
namespace L
export Holant.LocalDrafts.Tractability.EOEvaluation.PairLift
  (Compatible restrict indicator compress lift_identity word_compress affine_lift product_lift)
end L
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} (f : Signature AlgebraicComplex n)


def points : Finset (Fin n→Bool) := Finset.univ.filter (fun x=>f x≠0)

@[simp] theorem mem_points (x : Fin n→Bool) : x∈points f ↔ f x≠0 := by
  simp [points]

theorem nonempty_points (hn : f≠0) : (points f).Nonempty := by
  obtain ⟨x,hx⟩ := Function.ne_iff.mp hn
  exact ⟨x,(mem_points f x).mpr hx⟩

variable (he : Signature.CentralSupport f) (hn : f≠0) (hc : Closed f)

def data : D.Data n where
  points := points f
  base := ⟨(nonempty_points f hn).choose,(nonempty_points f hn).choose_spec⟩
  closed := by
    intro a ha b hb c hcc
    exact (mem_points f _).mpr (hc a b c ((mem_points f _).mp ha)
      ((mem_points f _).mp hb) ((mem_points f _).mp hcc))
  central := by
    intro x hx
    have hnx : f x≠0 := (mem_points f x).mp hx
    have hw : 2*Holant.weight x=n := by
      by_contra hw
      exact hnx (he x hw)
    unfold charge
    omega

def pairing : OrientedPerfectPairing n := PC.pairing (data f he hn hc)

theorem pairing_count : 2*(pairing f he hn hc).count=n := PC.twice_count (data f he hn hc)

/-- Opposite paired incidences are derived for every original supported word. -/
theorem covers (x : Fin n→Bool) (hx : f x≠0) : L.Compatible (pairing f he hn hc) x :=
  PC.covers (data f he hn hc) x ((mem_points f x).mpr hx)

/-- This is a coefficient-wise equality with the original tensor, not a
zero-extension assumed to be physically realizable. -/
theorem full_restriction : L.restrict (pairing f he hn hc) f=f := by
  funext x
  by_cases hx : f x=0
  · simp [L.restrict,hx]
  · exact if_pos (covers f he hn hc x hx)

theorem exact_paired_lift : f=fun x=>
    (pairing f he hn hc).restrict f (L.compress (pairing f he hn hc) x)*
      L.indicator (pairing f he hn hc) x := by
  rw [←L.lift_identity,full_restriction]

/-- Every original class witness restricts along any oriented pairing. -/
theorem all_pairings_of_class (C : EOClass) (h : C.Holds f) :
    EONegativeWitness.Pairings C ⟨n,f⟩ := by
  intro p
  cases C with
  | affine => exact h.precompose p.word (EOBinaryPlaneTract.pairing_affine p)
  | product => exact EOBinaryPlaneTract.product_signed p.ports.symm h

/-- On this derived whole-support pairing, a class witness lifts back to the
literal original signature. -/
theorem original_class (C : EOClass) (h : C.Holds ((pairing f he hn hc).restrict f)) : C.Holds f := by
  have hl := Holant.LocalDrafts.Tractability.EOEvaluation.PairLift.class_lift
    (pairing f he hn hc) C h
  rwa [full_restriction] at hl

theorem class_iff (C : EOClass) : C.Holds ((pairing f he hn hc).restrict f) ↔
    EONegativeWitness.Pairings C ⟨n,f⟩ := by
  constructor
  · intro h
    exact all_pairings_of_class f C (original_class f he hn hc C h)
  · intro h
    exact h (pairing f he hn hc)

/-- Class failure is inherited by the internally produced support-covering
pairing; the caller supplies no desired pairing or endpoint. -/
theorem pairing_failure (C : EOClass) (h : ¬EONegativeWitness.Pairings C ⟨n,f⟩) :
    ¬C.Holds ((pairing f he hn hc).restrict f) :=
  fun hh=>h ((class_iff f he hn hc C).mp hh)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeClosedSupport
