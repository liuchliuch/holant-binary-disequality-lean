import Holant.Certificates.OppositeIcosahedral.NativeExpansion
import Holant.Certificates.OppositeIcosahedral.PhysicalDictionary

namespace Holant.Certificates.OppositeIcosahedral
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Only original vertex labels and the fixed actual opposite representatives
occur in the compiled network. No analytical tensor or basis matrix is a label. -/
def fixedNativeLabels {n : ℕ} (s : NetworkShape n)
    (f : (v : Fin s.vertices)→Signature ℂ (s.arity v)) (i : Fin s.edges→Fin 60) :
    (v : NativeVertex s)→Signature ℂ (expansionArity s v)
  | .inl v => f v
  | .inr e => MatchingContractionClosure.binarySignature (oppositeRepresentative (binaryIndex (kernelIndex (i e))))

def fixedNativeFinite {n : ℕ} (s : NetworkShape n)
    (f : (v : Fin s.vertices)→Signature ℂ (s.arity v)) (i : Fin s.edges→Fin 60) :
    FiniteNetwork ℂ (NativeVertex s) (Fin s.edges×Bool) n where
  arity := expansionArity s
  ports := expansionPorts s
  vertex := fixedNativeLabels s f i
  edge := fun _ => Signature.disequality

def fixedNativeNetwork {n : ℕ} (s : NetworkShape n)
    (f : (v : Fin s.vertices)→Signature ℂ (s.arity v)) (i : Fin s.edges→Fin 60) : Network ℂ n :=
  (fixedNativeFinite s f i).toNetwork

def vertexScale {n : ℕ} (s : NetworkShape n) (i : Fin s.edges→Fin 60) : NativeVertex s→ℂ :=
  Sum.elim (fun _ => 1) (fun e => binaryScale (kernelIndex (i e)))

theorem finite_vertex_scalars {V E : Type*} [Fintype V] [Fintype E] {n : ℕ}
    (N : FiniteNetwork ℂ V E n) (c : V→ℂ) :
    (FiniteNetwork.mk N.arity N.ports (fun v => c v • N.vertex v) N.edge).denote=
      (∏v,c v) • N.denote := by
  classical
  funext x
  simp only [FiniteNetwork.denote,Pi.smul_apply,smul_eq_mul,Finset.prod_mul_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem expanded_labels_exact {n : ℕ} (s : NetworkShape n)
    (f : (v : Fin s.vertices)→Signature ℂ (s.arity v)) (i : Fin s.edges→Fin 60) :
    expansionLabels (Network.mk s f (fun e => oppositeRepresentative (kernelIndex (i e))))=
      (fun v => vertexScale s i v • fixedNativeLabels s f i v) := by
  funext v
  cases v with
  | inl v => simp [expansionLabels,vertexScale,fixedNativeLabels]
  | inr e =>
    change MatchingContractionClosure.binarySignature (MatchingContractionClosure.nativePair
      (oppositeRepresentative (kernelIndex (i e))))=binaryScale (kernelIndex (i e)) •
        MatchingContractionClosure.binarySignature (oppositeRepresentative (binaryIndex (kernelIndex (i e))))
    funext x
    change MatchingContractionClosure.nativePair (oppositeRepresentative (kernelIndex (i e))) (x 0) (x 1)=_
    rw [native_pair_fixed]
    rfl

theorem fixed_native_scaling {n : ℕ} (s : NetworkShape n)
    (f : (v : Fin s.vertices)→Signature ℂ (s.arity v)) (i : Fin s.edges→Fin 60) :
    (Network.mk s f (fun e => oppositeRepresentative (kernelIndex (i e)))).denote=
      (∏e,binaryScale (kernelIndex (i e))) • (fixedNativeNetwork s f i).denote := by
  let N : Network ℂ n := ⟨s,f,fun e => oppositeRepresentative (kernelIndex (i e))⟩
  have hn := nativeExpansion_denote N
  rw [nativeExpansion,FiniteNetwork.denote_toNetwork] at hn
  have he : expansionFinite N=
      FiniteNetwork.mk (fixedNativeFinite s f i).arity (fixedNativeFinite s f i).ports
        (fun v => vertexScale s i v • (fixedNativeFinite s f i).vertex v) (fixedNativeFinite s f i).edge := by
    exact congrArg (fun labels : (v : NativeVertex s)→Signature ℂ (expansionArity s v) =>
      FiniteNetwork.mk (expansionArity s) (expansionPorts s) labels
        (fun _ : Fin s.edges×Bool => Signature.disequality)) (expanded_labels_exact s f i)
  rw [he,finite_vertex_scalars] at hn
  have hprod : (∏v : NativeVertex s,vertexScale s i v)=∏e,binaryScale (kernelIndex (i e)) := by
    simp [vertexScale,NativeVertex,Fintype.prod_sum_type]
  rw [hprod] at hn
  rw [fixedNativeNetwork,FiniteNetwork.denote_toNetwork]
  exact hn.symm

def realizationScale {m : ℕ} (i : Fin m→Fin 60) : ℂ :=
  (∏e,binaryScale (kernelIndex (i e)))⁻¹*(∏e,(kernelScale (i e))⁻¹)

theorem realizationScale_ne_zero {m : ℕ} (i : Fin m→Fin 60) : realizationScale i≠0 := by
  apply mul_ne_zero
  · exact inv_ne_zero (Finset.prod_ne_zero_iff.mpr (fun e _ => binaryScale_ne_zero (kernelIndex (i e))))
  · exact network_scale_ne_zero i

/-- Complete original-resource native-X covariance, with every kernel and
binary representative scalar retained in one explicitly defined product. -/
theorem fixedNativeNetwork_denote {n : ℕ} (s : NetworkShape n)
    (f : (v : Fin s.vertices)→Signature ℂ (s.arity v)) (i : Fin s.edges→Fin 60) :
    (fixedNativeNetwork s f i).denote=realizationScale i •
      transport (analyticalNetwork s f (fun e => standardRepresentative (i e))).denote := by
  have hb := fixed_native_scaling s f i
  have hk := fixed_network_covariance s f i
  have hn : (∏e,binaryScale (kernelIndex (i e)))≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun e _ => binaryScale_ne_zero (kernelIndex (i e)))
  calc (fixedNativeNetwork s f i).denote=
      (∏e,binaryScale (kernelIndex (i e)))⁻¹ •
        ((∏e,binaryScale (kernelIndex (i e))) • (fixedNativeNetwork s f i).denote) := by simp [smul_smul,hn]
    _=(∏e,binaryScale (kernelIndex (i e)))⁻¹ •
      ((∏e,(kernelScale (i e))⁻¹) • transport (analyticalNetwork s f (fun e => standardRepresentative (i e))).denote) :=
        by rw [←hb,hk]
    _=_ := by rw [smul_smul]; rfl

def fixedResources {n : ℕ} (s : NetworkShape n)
    (f : (v : Fin s.vertices)→Signature ℂ (s.arity v)) : SignatureFamily ℂ :=
  {p | (∃v : Fin s.vertices,p=⟨s.arity v,f v⟩) ∨
    ∃j : Fin 60,p=⟨2,MatchingContractionClosure.binarySignature (oppositeRepresentative j)⟩}

theorem fixedNativeNetwork_realizes {n : ℕ} (s : NetworkShape n)
    (f : (v : Fin s.vertices)→Signature ℂ (s.arity v)) (i : Fin s.edges→Fin 60) :
    Gadget.Realizes (fixedResources s f) .disequality (realizationScale i •
      transport (analyticalNetwork s f (fun e => standardRepresentative (i e))).denote) := by
  have hh := Gadget.realizes_network (fixedNativeNetwork s f i) (fixedResources s f) .disequality
    (by
      intro v
      change (⟨_,fixedNativeLabels s f i ((Fintype.equivFin (NativeVertex s)).symm v)⟩ : AnySignature ℂ)∈_
      cases he : (Fintype.equivFin (NativeVertex s)).symm v with
      | inl w => exact Or.inl ⟨w,rfl⟩
      | inr e => exact Or.inr ⟨binaryIndex (kernelIndex (i e)),rfl⟩)
    (by intro e; rfl)
  rwa [fixedNativeNetwork_denote] at hh

/-- The ambient source family is unchanged whenever it supplies the original
occurrences and its fixed actual group binaries. In particular a supplied I is
still the same literal resource; no basis-transformed copy is added. -/
theorem fixed_family_realizes {n : ℕ} (family : SignatureFamily ℂ) (s : NetworkShape n)
    (f : (v : Fin s.vertices)→Signature ℂ (s.arity v)) (i : Fin s.edges→Fin 60)
    (hf : ∀v,(⟨s.arity v,f v⟩ : AnySignature ℂ)∈family)
    (hG : ∀j : Fin 60,(⟨2,MatchingContractionClosure.binarySignature (oppositeRepresentative j)⟩ : AnySignature ℂ)∈family) :
    Gadget.Realizes family .disequality (realizationScale i •
      transport (analyticalNetwork s f (fun e => standardRepresentative (i e))).denote) := by
  apply (fixedNativeNetwork_realizes s f i).mono
  rintro p (⟨v,rfl⟩|⟨j,rfl⟩)
  · exact hf v
  · exact hG j


theorem original_vertex_unchanged {n : ℕ} (s : NetworkShape n)
    (f : (v : Fin s.vertices)→Signature ℂ (s.arity v)) (i : Fin s.edges→Fin 60) (v : Fin s.vertices) :
    fixedNativeLabels s f i (.inl v)=f v := rfl

theorem fixedNativeNetwork_vertices {n : ℕ} (s : NetworkShape n)
    (f : (v : Fin s.vertices)→Signature ℂ (s.arity v)) (i : Fin s.edges→Fin 60) :
    (fixedNativeNetwork s f i).shape.vertices=s.vertices+s.edges := by
  simp [fixedNativeNetwork,FiniteNetwork.toNetwork,NativeVertex]

theorem fixedNativeNetwork_edges {n : ℕ} (s : NetworkShape n)
    (f : (v : Fin s.vertices)→Signature ℂ (s.arity v)) (i : Fin s.edges→Fin 60) :
    (fixedNativeNetwork s f i).shape.edges=2*s.edges := by
  simp [fixedNativeNetwork,FiniteNetwork.toNetwork,Nat.mul_comm]

end
end Holant.Certificates.OppositeIcosahedral
