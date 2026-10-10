import Holant.Certificates.PlatonicIncidence.DomainGraph
import Holant.Certificates.PlatonicIncidence.CoefficientEquivs
import Mathlib.Algebra.Module.Submodule.Equiv

/-! The public graph is defined directly from complex spans. All marked and
external deletion conclusions are transported through actual proved linear
equivalences, including the retained-I kappa dictionary. -/
namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def MatrixSecant {n : ℕ} (U : Fin n→Mat) (S : Finset (Fin n)) : Prop :=
  ∃i j : Fin n,i≠j ∧ ∀k : Fin n,k∈S ↔ U k∈Submodule.span ℂ ({U i,U j} : Set Mat)

def matrixGraph {n : ℕ} (U : Fin n→Mat) : SimpleGraph (Fin n) where
  Adj i j := i≠j ∧ ∃S : Finset (Fin n),MatrixSecant U S ∧ 3≤S.card ∧ i∈S ∧ j∈S
  symm := ⟨by
    rintro i j ⟨hij,S,hS,hc,hi,hj⟩
    exact ⟨hij.symm,S,hS,hc,hj,hi⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

theorem matrixSecant_transport {n : ℕ} (e : Mat ≃ₗ[ℂ] Mat) (U : Fin n→Mat)
    (S : Finset (Fin n)) : MatrixSecant (fun i => e (U i)) S ↔ MatrixSecant U S := by
  simp only [MatrixSecant,equiv_span_pair]

theorem matrixGraph_transport {n : ℕ} (e : Mat ≃ₗ[ℂ] Mat) (U : Fin n→Mat) :
    matrixGraph (fun i => e (U i))=matrixGraph U := by
  ext i j
  simp only [matrixGraph,matrixSecant_transport]

theorem matrixGraph_standard (g : PlatonicModel) : matrixGraph (representative g)=domainGraph g := by
  ext i j
  exact (domainGraph_semantics g i j).symm

theorem transformed_kernel_deleted_connected (g : PlatonicModel) (e : Mat ≃ₗ[ℂ] Mat)
    (W : Submodule ℂ Mat) (hW : Module.finrank ℂ W≤2) :
    ((matrixGraph (fun i => e (representative g i))).induce
      {i | e (representative g i)∉W}).Connected := by
  have hp : Module.finrank ℂ (W.comap e.toLinearMap)≤2 := by
    rw [(e.ofSubmodule' W).finrank_eq]
    exact hW
  have hc := kernel_deleted_connected g (W.comap e.toLinearMap) hp
  rw [matrixGraph_transport,matrixGraph_standard]
  exact hc

theorem marked_kernel_deleted_connected (f : OctahedralSeparator.Form)
    (W : Submodule ℂ Mat) (hW : Module.finrank ℂ W≤2) :
    ((matrixGraph (fun i => OctahedralSeparator.complexTheta f (representative .octahedral i))).induce
      {i | OctahedralSeparator.complexTheta f (representative .octahedral i)∉W}).Connected :=
  transformed_kernel_deleted_connected .octahedral (thetaEquiv f) W hW

theorem external_kernel_deleted_connected (W : Submodule ℂ Mat)
    (hW : Module.finrank ℂ W≤2) :
    ((matrixGraph External.representative).induce {i | External.representative i∉W}).Connected := by
  have h := transformed_kernel_deleted_connected .tetrahedral (thetaEquiv 2) W hW
  let P : (Fin 12→Mat)→Prop := fun U => ((matrixGraph U).induce {i | U i∉W}).Connected
  have h' : P (fun i => thetaEquiv 2 (goldenMatrix (tetrahedralRaw i))) := h
  have he : (fun i : Fin 12 => thetaEquiv 2 (goldenMatrix (tetrahedralRaw i)))=External.representative :=
    funext (fun i => external_dictionary i)
  exact Eq.mp (congrArg P he) h'

theorem opposite_kernel_deleted_connected (W : Submodule ℂ Mat)
    (hW : Module.finrank ℂ W≤2) :
    ((matrixGraph OppositeIcosahedral.oppositeRepresentative).induce
      {i | OppositeIcosahedral.oppositeRepresentative i∉W}).Connected := by
  have h := transformed_kernel_deleted_connected .icosahedral oppositeEquiv W hW
  change ((matrixGraph (fun i : Fin 60 => oppositeEquiv (representative .icosahedral i))).induce
    {i | oppositeEquiv (representative .icosahedral i)∉W}).Connected at h
  simp_rw [opposite_dictionary] at h
  exact h

/-- The same full assertion using the source's literal retained-I kernels,
whose exact projective bijection/scalars are exposed in retained_I_kernel_dictionary. -/
theorem retained_I_kernel_deleted_connected (W : Submodule ℂ Mat)
    (hW : Module.finrank ℂ W≤2) :
    ((matrixGraph (fun i => OppositeIcosahedral.kappa (representative .icosahedral i))).induce
      {i | OppositeIcosahedral.kappa (representative .icosahedral i)∉W}).Connected :=
  transformed_kernel_deleted_connected .icosahedral kappaEquiv W hW

end
end Holant.Certificates.PlatonicIncidence
