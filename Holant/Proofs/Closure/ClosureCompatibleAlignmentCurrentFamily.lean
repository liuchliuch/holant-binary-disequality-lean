import Holant.Proofs.Closure.ClosureCompatibleAlignmentCurrentBound
import Holant.Proofs.Closure.ClosureCompatibleAlignmentParityProfiles

/-! One literal common tuple family for EVERY actual nonzero CURRENT root
sample.  Zero samples stay outside the nonzero subtype and are still covered
by the raw-card factories.  An anchor is constructed from the original
nonzero tensor and two real roots; it is not a caller-supplied classifier. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.Dihedral.CompatibleClosure Holant.Dihedral.CompatibleCoefficientLine

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable {r : ℕ} (f : Signature (OI.K G) (2*r+4))
variable (order : Equiv.Perm (Fin (2*r+4)))

def Sample := {i : Bool × {t : Scalar // Roots N.m t} //
  normalizedCurrentCard G P torsion N f order i.1 i.2 ≠ 0}

theorem sample_nonempty (nonzero : f ≠ 0) : Nonempty (Sample G P torsion N f order) := by
  classical
  by_contra none
  have zero (γ : Bool) (t : {t : Scalar // Roots N.m t}) :
      normalizedCurrentCard G P torsion N f order γ t = 0 := by
    by_contra live
    exact none ⟨⟨(γ,t),live⟩⟩
  obtain ⟨w,live⟩ : ∃ w,f w ≠ 0 := by
    by_contra empty
    push_neg at empty
    exact nonzero (funext empty)
  let γ := w (order 0) ^^ w (order 1)
  let x := residualPairN order w
  let oneRoot : {t : Scalar // Roots N.m t} := ⟨1,Roots.one N.m⟩
  obtain ⟨t,square⟩ := root_square_avoids N.range 1
  have different : t.val ≠ 1 := fun equal => square (by simp [equal])
  let u := ClosureSourceRows.embedding G (f (fillPairN order false γ x))
  let v := ClosureSourceRows.embedding G (f (fillPairN order true γ x))
  have first : u+v=0 := by
    have h := congrFun (zero γ oneRoot) x
    rw [normalizedCurrentCard_entry] at h
    simpa only [oneRoot,one_mul,Pi.zero_apply,u,v] using h
  have second : u+t.val*v=0 := by
    have h := congrFun (zero γ t) x
    rw [normalizedCurrentCard_entry] at h
    exact h
  have hv : v = 0 := by
    have product : (t.val-1)*v=0 := by linear_combination second-first
    exact (mul_eq_zero.mp product).resolve_left (sub_ne_zero.mpr different)
  have hu : u = 0 := by linear_combination first-hv
  have endpoint : f (fillPairN order (w (order 0)) γ x) = 0 := by
    cases value : w (order 0)
    · exact (map_eq_zero (ClosureSourceRows.embedding G)).mp hu
    · exact (map_eq_zero (ClosureSourceRows.embedding G)).mp hv
  have reconstruct : fillPairN order (w (order 0)) γ x = w := fillPairN_reconstruct order w
  exact live (reconstruct ▸ endpoint)

def canonicalAnchor (nonzero : f ≠ 0) : Sample G P torsion N f order :=
  Classical.choice (sample_nonempty G P torsion N f order nonzero)

variable (stable : ∀ g ∈ rawDeck P.family torsion f,
  Holant.Certificates.MatchingContractionClosure.MatchingOrZero (actualTransfers P.family) g)

def selectedSample (i : Sample G P torsion N f order) :
    CurrentSelectedCard G P torsion N f order i.val.1 i.val.2 :=
  selectCurrentCard G P torsion N f order i.val.1 i.val.2 stable i.property

variable (anchor : Sample G P torsion N f order)

def familyPorts : (Fin (r+1) × Bool) ≃ Fin (2*r+2) :=
  (selectedSample G P torsion N f order stable anchor).ports

def familyTables (i : Sample G P torsion N f order) : Fin (r+1) → Mat :=
  alignedFactor (familyPorts G P torsion N f order stable anchor)
    (selectedSample G P torsion N f order stable i).ports
    (selectedSample G P torsion N f order stable i).factors

def familyCoefficient (i : Sample G P torsion N f order) : Scalar :=
  (selectedSample G P torsion N f order stable i).algebraic.scalar

def familyOriginalCoefficient (i : Sample G P torsion N f order) : OI.K G :=
  (ClosureSixPort.algebraicCardCoefficient G P torsion N i.val.1 i.val.2)⁻¹ *
    (selectedSample G P torsion N f order stable i).native.scalar

theorem familyCoefficient_original (i : Sample G P torsion N f order) :
    familyCoefficient G P torsion N f order stable i =
      ClosureSourceRows.embedding G (familyOriginalCoefficient G P torsion N f order stable i) := by
  simp only [familyCoefficient,CurrentSelectedCard.algebraic,familyOriginalCoefficient,map_mul,map_inv₀]

theorem familyTables_self (e : Fin (r+1)) :
    familyTables G P torsion N f order stable anchor anchor e =
      (selectedSample G P torsion N f order stable anchor).factors e := by
  simp [familyTables,familyPorts,alignedFactor,edgeIndex,edgeReversed]

theorem familyTables_anchor_original (e : Fin (r+1)) :
    familyTables G P torsion N f order stable anchor anchor e =
      ((selectedSample G P torsion N f order stable anchor).native.matrix
        ((finCongr (selectedSample G P torsion N f order stable anchor).edgeCount).symm e)).map
          (ClosureSourceRows.embedding G) := by
  rw [familyTables_self]
  rfl

theorem familyTables_member (i : Sample G P torsion N f order) (e : Fin (r+1)) :
    familyTables G P torsion N f order stable anchor i e ∈ groupM N.m :=
  alignedFactor_group (by have := N.range; omega) _ _ _
    (selectedSample G P torsion N f order stable i).factors_member e

theorem familyCoefficient_nonzero (i : Sample G P torsion N f order) :
    familyCoefficient G P torsion N f order stable i ≠ 0 :=
  (selectedSample G P torsion N f order stable i).algebraic_scalar_nonzero

theorem family_card_equation (large : 2 ≤ r) (i : Sample G P torsion N f order) :
    normalizedCurrentCard G P torsion N f order i.val.1 i.val.2 =
      productValue (familyPorts G P torsion N f order stable anchor)
        (familyTables G P torsion N f order stable anchor i)
        (familyCoefficient G P torsion N f order stable i) := by
  let A := selectedSample G P torsion N f order stable anchor
  let S := selectedSample G P torsion N f order stable i
  have same := current_selected_matchings_equal G P torsion N f order large stable
    anchor.val.1 i.val.1 anchor.val.2 i.val.2 A S
  have source := S.coefficient_product
  rw [← aligned_product A.ports S.ports same S.factors S.algebraic.scalar] at source
  exact source

/-- Pairwise at-most-one line distance is a conclusion from one actual
outside contraction, for this SAME common original edge tuple family. -/
theorem family_distance_le_one (large : 2 ≤ r) (i j : Sample G P torsion N f order)
    (e d : Fin (r+1)) (different : e ≠ d) :
    ProjectivelyEqual (familyTables G P torsion N f order stable anchor j e)
      (familyTables G P torsion N f order stable anchor i e) ∨
    ProjectivelyEqual (familyTables G P torsion N f order stable anchor j d)
      (familyTables G P torsion N f order stable anchor i d) :=
  common_matching_one_step_bound N.range large _
    (fun cut γ t => current_outside_card_cases G P torsion N f stable order cut γ t)
    _ _ (familyPorts G P torsion N f order stable anchor)
    (familyTables G P torsion N f order stable anchor i)
    (familyTables G P torsion N f order stable anchor j) _ _
    (familyTables_member G P torsion N f order stable anchor i)
    (familyTables_member G P torsion N f order stable anchor j)
    (familyCoefficient_nonzero G P torsion N f order stable i)
    (familyCoefficient_nonzero G P torsion N f order stable j)
    (family_card_equation G P torsion N f order stable anchor large i)
    (family_card_equation G P torsion N f order stable anchor large j) e d different

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
