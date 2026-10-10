import Holant.Dihedral.SixPortBase.Pencil
import Holant.Dihedral.SectorRuling.PhysicalSectors

/-! The three sector alternatives are consequences of the actual sampled
cards, with exact endpoint coefficients and the original residual port map. -/
noncomputable section
namespace Holant.Dihedral.SixPortBase
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Dihedral.SectorRuling

structure ProportionalSector (m : ℕ) (U V : Signature Scalar 4) where
  ports : Ports
  fixedEdge : Fin 2
  varyingEdge : Fin 2
  distinct : fixedEdge ≠ varyingEdge
  fixed : Mat
  varying : Mat
  fixed_mem : fixed ∈ groupM m
  varying_mem : varying ∈ groupM m
  first : Scalar
  second : Scalar
  nonzero : first ≠ 0 ∨ second ≠ 0
  first_exact : U=first • twoProduct ports fixedEdge varyingEdge fixed varying
  second_exact : V=second • twoProduct ports fixedEdge varyingEdge fixed varying

structure ComplementarySector (m : ℕ) (U V : Signature Scalar 4) where
  ports : Ports
  fixedEdge : Fin 2
  varyingEdge : Fin 2
  distinct : fixedEdge ≠ varyingEdge
  fixed : Mat
  fixed_mem : fixed ∈ groupM m
  parity : Bool
  orientation : Bool
  first : Scalar
  second : Scalar
  first_ne_zero : first ≠ 0
  second_ne_zero : second ≠ 0
  ratio_root : Roots m (second/first)
  first_exact : U=twoProduct ports fixedEdge varyingEdge fixed (scale first (axis parity orientation))
  second_exact : V=twoProduct ports fixedEdge varyingEdge fixed (scale second (axis parity (!orientation)))

 def SectorType (m : ℕ) (U V : Signature Scalar 4) : Prop :=
  (U=0 ∧ V=0) ∨ Nonempty (ProportionalSector m U V) ∨ Nonempty (ComplementarySector m U V)

 theorem source_sector_type {m : ℕ} (hm : 3≤m) (U V : Signature Scalar 4)
    (hs : ∀ t,Roots m t → tensorPencil U V t=0 ∨ MatchingSample m 2 (tensorPencil U V t)) :
    SectorType m U V := by
  obtain ⟨D⟩ := exact_pencil hm U V hs
  rcases binary_type hm D.first D.second D.samples with hz|hp|hc
  · left
    constructor
    · rw [D.first_exact,hz.1]
      funext x
      simp [twoProduct]
    · rw [D.second_exact,hz.2]
      funext x
      simp [twoProduct]
  · right; left
    obtain ⟨Q,hQ,a,b,hab,ha,hb⟩ := hp
    refine ⟨⟨D.ports,D.fixedEdge,D.varyingEdge,D.distinct,D.fixed,Q,D.fixed_mem,hQ,a,b,hab,?_,?_⟩⟩
    · refine D.first_exact.trans ?_
      rw [ha]
      funext x
      simp only [twoProduct,scale,Pi.smul_apply,smul_eq_mul]
      ring
    · refine D.second_exact.trans ?_
      rw [hb]
      funext x
      simp only [twoProduct,scale,Pi.smul_apply,smul_eq_mul]
      ring
  · right; right
    obtain ⟨p,r,a,b,ha,hb,hr,hA,hB⟩ := hc
    exact ⟨⟨D.ports,D.fixedEdge,D.varyingEdge,D.distinct,D.fixed,D.fixed_mem,
      p,r,a,b,ha,hb,hr,D.first_exact.trans (congrArg _ hA),D.second_exact.trans (congrArg _ hB)⟩⟩

end Holant.Dihedral.SixPortBase
