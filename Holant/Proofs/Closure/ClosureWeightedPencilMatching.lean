import Holant.Proofs.Closure.ClosureWeightedPencilSupport
import Holant.Dihedral.TwoCardLocalization.DistinctProducts

/-! The four-port live sample matching is recovered from the internally
proved monomial support. This is independent of the higher-source matching
theorem, so it is usable at the genuine six-port residual boundary.
New proof, awaiting strict kernel validation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
open Holant Holant.Projective ClosureRootPencil
open Holant.Certificates.MatchingContractionClosure
open Holant.Dihedral.TwoCardLocalization
open Holant.Pauli.ExoticKlein

def productMatching {k : ℕ} {f : Signature ℂ 4} (P : Product k f) : Matching (Fin 4) 2 :=
  ⟨P.ports⟩

theorem product_mate_port_of_support {k : ℕ} {f g : Signature ℂ 4}
    (P : Product k f) (E : Product k g) (supported : support f ⊆ support g)
    (e : Fin 2) (b : Bool) :
    (productMatching P).mate (E.ports (e,b))=E.ports (e,!b) := by
  have all (a : Fin 2 → Bool) : g (P.word a)≠0 :=
    (mem_support g _).mp (supported ((mem_support f _).mpr (P.word_supported a)))
  have index : (P.ports.symm (E.ports (e,b))).1=
      (P.ports.symm (E.ports (e,!b))).1 := by
    cases b
    · exact P.anchor_index_eq E all e
    · exact (P.anchor_index_eq E all e).symm
  have different : (P.ports.symm (E.ports (e,b))).2≠
      (P.ports.symm (E.ports (e,!b))).2 := by
    intro sides
    have equal := congrArg P.ports (Prod.ext index sides)
    simp only [Equiv.apply_symm_apply] at equal
    have pair := E.ports.injective equal
    have impossible := congrArg Prod.snd pair
    cases b <;> contradiction
  have opposite : (P.ports.symm (E.ports (e,!b))).2=
      !(P.ports.symm (E.ports (e,b))).2 := by
    cases first : (P.ports.symm (E.ports (e,b))).2 <;>
      cases second : (P.ports.symm (E.ports (e,!b))).2 <;> simp_all
  have coordinates : P.ports.symm (E.ports (e,!b))=
      ((P.ports.symm (E.ports (e,b))).1,!(P.ports.symm (E.ports (e,b))).2) :=
    Prod.ext index.symm opposite
  calc
    (productMatching P).mate (E.ports (e,b))=
        (productMatching P).mate (P.ports (P.ports.symm (E.ports (e,b)))) := by
      rw [P.ports.apply_symm_apply]
    _=P.ports ((P.ports.symm (E.ports (e,b))).1,!(P.ports.symm (E.ports (e,b))).2) :=
      Matching.mate_port (productMatching P) _ _
    _=E.ports (e,!b) := by
      rw [←coordinates,P.ports.apply_symm_apply]

theorem product_mate_equal {k : ℕ} {f g : Signature ℂ 4}
    (P : Product k f) (E : Product k g) (supported : support f ⊆ support g) :
    (productMatching P).mate=(productMatching E).mate := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨e,b⟩,rfl⟩ := E.ports.surjective x
  exact (product_mate_port_of_support P E supported e b).trans
    (Matching.mate_port (productMatching E) e b).symm

/-- This gate concerns the literal presentations supplied by the sample
predicate, not independently selected equal-value presentations. -/
theorem presentations_same_mate (M N : Presentation ℂ (Fin 4))
    (monomialM : ∀ e,IsRootMonomial 0 (M.matrix e))
    (monomialN : ∀ e,IsRootMonomial 0 (N.matrix e))
    (nonzeroM : M.scalar≠0) (nonzeroN : N.scalar≠0)
    (supported : support M.tensor ⊆ support N.tensor) :
    (presentationMatching M).mate=(presentationMatching N).mate := by
  have edgesM : M.edges=2 := by
    have h := Fintype.card_congr M.ports
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at h
    omega
  have edgesN : N.edges=2 := by
    have h := Fintype.card_congr N.ports
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at h
    omega
  cases M with
  | mk n p A c =>
    dsimp only at edgesM
    subst n
    cases N with
    | mk n q B d =>
      dsimp only at edgesN
      subst n
      let P : Product 0 (Presentation.mk 2 p A c).tensor := ⟨p,A,c,nonzeroM,monomialM,rfl⟩
      let E : Product 0 (Presentation.mk 2 q B d).tensor := ⟨q,B,d,nonzeroN,monomialN,rfl⟩
      exact product_mate_equal P E supported

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
