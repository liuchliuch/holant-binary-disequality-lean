import Holant.Platonic.TetrahedralLocalization.Physical

/-! Source Proposition9.22, physical tetrahedral localization. Both its actual
one-card assertion and finite one-original-g descent are proved, including
actual B_g representatives, their nonzero scalars, exact native-X graph
semantics, nonaffinity, factor exits and a linear number of binary vertices.

The proof is stronger than the marked-state assertion: no marked-state or
terminal/restart premise is needed. It can continue until a small nonaffine
output or a genuine factor of a realized descendant. Thus the source's
additional terminal and strict complete-group restart exits remain allowed.
No factor itself is asserted to be directly realized.
-/
namespace Holant.Platonic.TetrahedralLocalization
open Holant Holant.Platonic.StabilizerShortening Holant.Platonic.StabilizerLine
open Holant.Certificates.MatchingContractionClosure Holant.Certificates.TetrahedralAffine
open Holant.Platonic.RainbowLocalization.Physical
open Holant.Pauli.ExoticKlein.Fiber
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {o n : ℕ} {Λ : SignatureFamily ℂ}

/-- The two native-X wires give the actual effective table X B_r X. -/
def actualPairCard (A : ActualKernelLift Λ tetrahedralKernels)
    (p : (Bool ⊕ Fin n) ≃ Fin o) (r : Representative) (f : Signature ℂ o) : Signature ℂ n :=
  pairCard p (nativePair (A.binary (actualChoice r))) f

theorem actual_effective_kernel (A : ActualKernelLift Λ tetrahedralKernels) (r : Representative) :
    nativePair (A.binary (actualChoice r))=A.scalar (actualChoice r) • complexKernel r := by
  rw [A.normalization,nativePair_smul]
  congr 1
  ext a b
  simp [actualChoice,nativePair_apply]

theorem pairCard_kernel_scale (p : (Bool ⊕ Fin n) ≃ Fin o) (K : Kernel ℂ)
    (c : ℂ) (f : Signature ℂ o) : pairCard p (c • K) f=c • pairCard p K f := by
  ext x
  simp [pairCard,mul_assoc,mul_add]

/-- Analytic normalization is transported by its exact actual nonzero scalar. -/
theorem actualPairCard_eq (A : ActualKernelLift Λ tetrahedralKernels)
    (p : (Bool ⊕ Fin n) ≃ Fin o) (r : Representative) (f : Signature ℂ o) :
    actualPairCard A p r f=A.scalar (actualChoice r) • pairCard p (complexKernel r) f := by
  rw [actualPairCard,actual_effective_kernel,pairCard_kernel_scale]

/-- A single actual card is a literal two-vertex native-X graph. -/
theorem actualPairCard_network (A : ActualKernelLift Λ tetrahedralKernels)
    (p : (Bool ⊕ Fin n) ≃ Fin o) (r : Representative) (g : Signature ℂ o) :
    (((PairCollection.empty o).add p r).network A g).denote=actualPairCard A p r g := by
  rw [PairCollection.denote,PairCollection.add_scale,PairCollection.empty_scale,
    mul_one,PairCollection.add_value,PairCollection.empty_value,actualPairCard_eq]

theorem actualPairCard_realizes (A : ActualKernelLift Λ tetrahedralKernels)
    (p : (Bool ⊕ Fin n) ≃ Fin o) (r : Representative) (g : Signature ℂ o) :
    Gadget.Realizes (actualResources A g) .disequality (actualPairCard A p r g) := by
  rw [←actualPairCard_network]
  exact ((PairCollection.empty o).add p r).realizes A g

/-- First assertion of Proposition9.22 in the actual retained representatives. -/
theorem source_actual_pair (A : ActualKernelLift Λ tetrahedralKernels)
    (g : Signature ℂ o) (ho : 10≤o)
    (hprime : ¬HasProperTensorFactor g) (hg : ¬ComplexAffine g) :
    ∃n : ℕ,∃p : (Bool ⊕ Fin n) ≃ Fin o,∃r : Representative,
      n+2=o ∧ p (.inl false)≠p (.inl true) ∧
      actualPairCard A p r g≠0 ∧ ¬ComplexAffine (actualPairCard A p r g) := by
  obtain ⟨n,p,r,he,hd,hn,ha⟩ := source_pair_with_arity g ho hprime hg
  refine ⟨n,p,r,he,hd,?_,?_⟩
  · rw [actualPairCard_eq]
    exact smul_ne_zero (A.scalar_ne_zero _) hn
  · rw [actualPairCard_eq]
    exact fun h => ha ((affine_complex_scale_iff _ (A.scalar_ne_zero _) _).mp h)

/-- The full finite physical localization, with one original-g occurrence,
actual binary labels, native wires and exact linear kernel count. The factor
alternative concerns the realized descendant, not an invented factor resource. -/
theorem source_physical_tetrahedral_localization
    (A : ActualKernelLift Λ tetrahedralKernels) (g : Signature ℂ o)
    (ho : 10≤o) (hg : ¬ComplexAffine g) :
    ∃n : ℕ,∃C : PairCollection o n,
      (C.network A g).denote≠0 ∧ ¬ComplexAffine (C.network A g).denote ∧
      (n≤8 ∨ HasProperTensorFactor (C.network A g).denote) ∧
      Gadget.Realizes (actualResources A g) .disequality (C.network A g).denote ∧
      C.scale A≠0 ∧ (C.network A g).denote=C.scale A • C.value g ∧
      n+2*Fintype.card C.Edge=o ∧ Fintype.card C.Edge=(o-n)/2 ∧
      Fintype.card C.Edge≤o/2 ∧
      (C.network A g).shape.vertices=(o-n)/2+1 ∧
      (C.network A g).shape.edges=2*((o-n)/2) ∧
      (Finset.univ.filter (fun v : Option C.Edge =>
        (nativeCollectionFinite C.ports (effectiveKernels A C.choices) g).arity v=o)).card=1 ∧
      (Finset.univ.filter (fun v : Option C.Edge =>
        (nativeCollectionFinite C.ports (effectiveKernels A C.choices) g).arity v=2)).card=(o-n)/2 := by
  obtain ⟨n,C,_,hC,hexit,hcount,hexact,hlinear⟩ := source_finite_descent g hg
  obtain ⟨hn,ha⟩ := C.nonaffine_actual A g hC
  exact ⟨n,C,hn,ha,C.actual_exit A g hexit,C.realizes A g,C.scale_ne_zero A,C.denote A g,
    hcount,hexact,hlinear,C.vertices A g,C.edges A g,
    C.original_vertex_count A g (by omega),C.binary_vertex_count A g (by omega)⟩

/-- Retained-family realization after actual gadget substitution. The additional
nonzero substitution scalar is kept, as are nonaffinity and the actual factor
alternative. The unexpanded graph still has the proved one-original-g counts. -/
theorem source_retained_tetrahedral_localization
    (A : ActualKernelLift Λ tetrahedralKernels) (g : Signature ℂ o)
    (hg : ¬ComplexAffine g) (hactual : Gadget.Realizes Λ .disequality g) :
    ∃n : ℕ,∃C : PairCollection o n,∃c : ℂ,c≠0 ∧
      Gadget.Realizes Λ .disequality (c • (C.network A g).denote) ∧
      c • (C.network A g).denote≠0 ∧ ¬ComplexAffine (c • (C.network A g).denote) ∧
      (n≤8 ∨ HasProperTensorFactor (c • (C.network A g).denote)) ∧
      Fintype.card C.Edge=(o-n)/2 ∧ Fintype.card C.Edge≤o/2 := by
  obtain ⟨n,C,_,hC,hexit,_,hexact,hlinear⟩ := source_finite_descent g hg
  obtain ⟨hn,ha⟩ := C.nonaffine_actual A g hC
  obtain ⟨c,hc,hr⟩ := C.realizesUpTo A g hactual
  refine ⟨n,C,c,hc,hr,smul_ne_zero hc hn,?_,?_,hexact,hlinear⟩
  · exact fun h => ha ((affine_complex_scale_iff _ hc _).mp h)
  · rcases C.actual_exit A g hexit with hs|hf
    · exact Or.inl hs
    · exact Or.inr (factor_scale _ c hc hf)

end
end Holant.Platonic.TetrahedralLocalization
