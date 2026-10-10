import Holant.Platonic.TetrahedralLocalization.Descent
import Holant.OpenNetworkComposition.ProjectiveSubstitution

/-! Source actual binaries, their nonzero scalars, native-X edges and exact
original-occurrence counts. Literal normalized kernels remain analytic tables;
all physical network labels are the supplied actual representatives B. -/
namespace Holant.Platonic.TetrahedralLocalization
open Holant Holant.Platonic.StabilizerShortening Holant.Platonic.StabilizerLine
open Holant.Certificates.MatchingContractionClosure Holant.Certificates.TetrahedralAffine
open Holant.Certificates.MatchingProductBridge
open Holant.Platonic.RainbowLocalization.Physical
open Holant.Pauli.ExoticKlein.Fiber
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {o m n : ℕ} {Λ : SignatureFamily ℂ}

/-- The twelve normalized table directions; actual physical lifts are separate. -/
def tetrahedralKernels : Set (Kernel ℂ) := {K | tetrahedralBase K}

def actualChoice (r : Representative) : tetrahedralKernels := ⟨complexKernel r,kernel_base r⟩

def PairCollection.choices (C : PairCollection o n) : C.Edge → tetrahedralKernels :=
  fun e => actualChoice (C.representative e)

def PairCollection.network (C : PairCollection o n)
    (A : ActualKernelLift Λ tetrahedralKernels) (f : Signature ℂ o) : Network ℂ n :=
  actualCollectionNetwork A C.choices C.ports f

def PairCollection.scale (C : PairCollection o n)
    (A : ActualKernelLift Λ tetrahedralKernels) : ℂ := realizationScale A C.choices

theorem PairCollection.scale_ne_zero (C : PairCollection o n)
    (A : ActualKernelLift Λ tetrahedralKernels) : C.scale A≠0 :=
  realizationScale_ne_zero A C.choices

@[simp] theorem PairCollection.empty_scale (A : ActualKernelLift Λ tetrahedralKernels) :
    (PairCollection.empty o).scale A=1 := by
  simp [PairCollection.scale,realizationScale,PairCollection.empty]

@[simp] theorem PairCollection.add_scale (C : PairCollection o m)
    (A : ActualKernelLift Λ tetrahedralKernels)
    (p : (Bool ⊕ Fin n) ≃ Fin m) (r : Representative) :
    (C.add p r).scale A=A.scalar (actualChoice r)*C.scale A := by
  simp [PairCollection.scale,realizationScale,PairCollection.add,PairCollection.choices,
    Fintype.prod_option]

/-- All per-binary scalars are retained as their literal finite product. -/
theorem PairCollection.denote (C : PairCollection o n)
    (A : ActualKernelLift Λ tetrahedralKernels) (f : Signature ℂ o) :
    (C.network A f).denote=C.scale A • C.value f :=
  actualCollection_denote A C.choices C.ports f

theorem factor_scale (f : Signature ℂ n) (c : ℂ) (hc : c≠0)
    (hf : HasProperTensorFactor f) : HasProperTensorFactor (c • f) := by
  obtain ⟨a,b,ha,hb,p,u,v,hu,hv,he⟩ := hf
  refine ⟨a,b,ha,hb,p,c • u,v,smul_ne_zero hc hu,hv,?_⟩
  rw [he]
  ext w
  simp [Tensor.reindex,Tensor.tensor,mul_assoc]

theorem PairCollection.nonaffine_actual (C : PairCollection o n)
    (A : ActualKernelLift Λ tetrahedralKernels) (f : Signature ℂ o)
    (hf : ¬ComplexAffine (C.value f)) :
    (C.network A f).denote≠0 ∧ ¬ComplexAffine (C.network A f).denote := by
  have ha : ¬ComplexAffine (C.network A f).denote := by
    rw [C.denote]
    exact fun h => hf ((affine_complex_scale_iff _ (C.scale_ne_zero A) _).mp h)
  exact ⟨fun hz => ha (hz ▸ affine_zero_complex),ha⟩

theorem PairCollection.actual_exit (C : PairCollection o n)
    (A : ActualKernelLift Λ tetrahedralKernels) (f : Signature ℂ o)
    (h : n≤8 ∨ HasProperTensorFactor (C.value f)) :
    n≤8 ∨ HasProperTensorFactor (C.network A f).denote := by
  rcases h with hn|hf
  · exact Or.inl hn
  · right
    rw [C.denote]
    exact factor_scale _ _ (C.scale_ne_zero A) hf

/-- Exactly one original-g label; all other vertices are the actual B labels. -/
theorem PairCollection.labels (C : PairCollection o n)
    (A : ActualKernelLift Λ tetrahedralKernels) (f : Signature ℂ o) :
    (nativeCollectionFinite C.ports (effectiveKernels A C.choices) f).vertex none=f ∧
      ∀e,(nativeCollectionFinite C.ports (effectiveKernels A C.choices) f).vertex (some e)=
        binarySignature (A.binary (C.choices e)) :=
  actualCollection_vertex_labels A C.choices C.ports f

theorem PairCollection.original_vertex_count (C : PairCollection o n)
    (A : ActualKernelLift Λ tetrahedralKernels) (f : Signature ℂ o) (ho : o≠2) :
    (Finset.univ.filter (fun v : Option C.Edge =>
      (nativeCollectionFinite C.ports (effectiveKernels A C.choices) f).arity v=o)).card=1 := by
  have he : Finset.univ.filter (fun v : Option C.Edge =>
      (nativeCollectionFinite C.ports (effectiveKernels A C.choices) f).arity v=o)={none} := by
    ext v
    cases v <;> simp [nativeCollectionFinite,collectionArity,Ne.symm ho]
  rw [he]
  simp

theorem PairCollection.binary_vertex_count (C : PairCollection o n)
    (A : ActualKernelLift Λ tetrahedralKernels) (f : Signature ℂ o) (ho : o≠2) :
    (Finset.univ.filter (fun v : Option C.Edge =>
      (nativeCollectionFinite C.ports (effectiveKernels A C.choices) f).arity v=2)).card=(o-n)/2 := by
  have he : Finset.univ.filter (fun v : Option C.Edge =>
      (nativeCollectionFinite C.ports (effectiveKernels A C.choices) f).arity v=2)=
        Finset.univ.erase none := by
    ext v
    cases v <;> simp [nativeCollectionFinite,collectionArity,ho]
  rw [he,Finset.card_erase_of_mem (Finset.mem_univ _)]
  simpa using C.exact_count

theorem PairCollection.vertices (C : PairCollection o n)
    (A : ActualKernelLift Λ tetrahedralKernels) (f : Signature ℂ o) :
    (C.network A f).shape.vertices=(o-n)/2+1 := by
  rw [PairCollection.network,actualCollection_vertices,C.exact_count]

theorem PairCollection.edges (C : PairCollection o n)
    (A : ActualKernelLift Λ tetrahedralKernels) (f : Signature ℂ o) :
    (C.network A f).shape.edges=2*((o-n)/2) := by
  rw [PairCollection.network,actualCollection_edges,C.exact_count]

/-- Every graph edge is the native disequality edge. -/
theorem PairCollection.native_edges (C : PairCollection o n)
    (A : ActualKernelLift Λ tetrahedralKernels) (f : Signature ℂ o) :
    ∀e,(C.network A f).edge e=Signature.disequality := fun _ => rfl

/-- The literal source resource family contains the original g and chosen
actual binary labels, never extracted factors or analytic Clifford frames. -/
def actualResources (A : ActualKernelLift Λ tetrahedralKernels)
    (f : Signature ℂ o) : SignatureFamily ℂ :=
  {s | s=⟨o,f⟩ ∨ ∃r : Representative,s=⟨2,binarySignature (A.binary (actualChoice r))⟩}

theorem PairCollection.realizes (C : PairCollection o n)
    (A : ActualKernelLift Λ tetrahedralKernels) (f : Signature ℂ o) :
    Gadget.Realizes (actualResources A f) .disequality (C.network A f).denote := by
  apply Gadget.realizes_network (C.network A f) (actualResources A f) .disequality
  · intro v
    let w := (Fintype.equivFin (Option C.Edge)).symm v
    change (⟨(nativeCollectionFinite C.ports (effectiveKernels A C.choices) f).arity w,
      (nativeCollectionFinite C.ports (effectiveKernels A C.choices) f).vertex w⟩ : AnySignature ℂ)
        ∈ actualResources A f
    cases w with
    | none => exact Or.inl rfl
    | some e =>
      apply Or.inr
      refine ⟨C.representative e,?_⟩
      change (⟨2,(nativeCollectionFinite C.ports (effectiveKernels A C.choices) f).vertex (some e)⟩ : AnySignature ℂ)=_
      rw [(C.labels A f).2 e]
      rfl
  · exact C.native_edges A f

/-- Actual retained-family gadgets can be substituted, with their nonzero
global realization scalar retained by the genuine substitution theorem. -/
theorem PairCollection.realizesUpTo (C : PairCollection o n)
    (A : ActualKernelLift Λ tetrahedralKernels) (f : Signature ℂ o)
    (hf : Gadget.Realizes Λ .disequality f) :
    Gadget.RealizesUpTo Λ .disequality (C.network A f).denote := by
  apply OpenNetworkComposition.realizes_network_upTo Λ (C.network A f)
  · intro v
    exact actualCollection_vertices_realizable A C.choices C.ports f hf
      ((Fintype.equivFin (Option C.Edge)).symm v)
  · exact C.native_edges A f
  · norm_num

end
end Holant.Platonic.TetrahedralLocalization
