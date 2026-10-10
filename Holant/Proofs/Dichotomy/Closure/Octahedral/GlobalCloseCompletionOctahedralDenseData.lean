import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralTerminals
import Holant.EightVertex.ProductAnchor.DenseNormalization

/-! Exact coefficient normalization of all three dense marked terminals.
The td normalization attaches its original diagonal representative on port0.
All sixteen tensor entries and the phase binary are kernel checked. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralDenseData
open Holant Holant.Certificates Holant.Certificates.OctahedralSeparator
open GlobalCloseCompletionOctahedralGeometry
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

def rawWeight : Form→Scalar := ![1,imag,1,(1+imag)/root]
def rawTarget (f : Form) : Signature Scalar 4 :=
  if f=0 then RankTwo.BaseTerminals.terminalShape false else
  if f=1 then RankTwo.BaseTerminals.terminalShape true else
  if f=2 then RankTwo.MixedEndpointBridge.mixedShape false imag else
    RankTwo.MixedEndpointBridge.mixedShape true imag

def rawDense (r : Scalar) : Signature Scalar 4 := fun x=>
  if Holant.weight x%2=0 then r^Holant.weight x else 0

def codes (f : Form) : Fin 4→Fin 24 := fun i=>if f=3 ∧ i=0 then 17 else 0
def slots (f : Form) : Fin 4→Mat := fun i=>theta f (standard (codes f i))
def cachedSlots (f : Form) : Fin 4 → Mat := fun i =>
  if f=3 ∧ i=0 then mat (1-imag) 0 0 (1+imag) else q 0

theorem slots_exact (f : Form) : slots f = cachedSlots f := by
  have hz (g : Form) : theta g (standard 0) = q 0 := by
    change mm (inverseConjugator g) (mm (q 0) (conjugator g)) = q 0
    rw [q0_mm,(conjugator_inverses g).2]
  funext i
  by_cases h : f=3 ∧ i=0
  · rcases h with ⟨rfl,rfl⟩
    decide +kernel
  · simp only [slots,codes,cachedSlots,if_neg h,hz]

def scalar (f : Form) : Scalar := if f=3 then 1-imag else 1

theorem scalar_nonzero (f : Form) : scalar f≠0 := by fin_cases f <;> decide +kernel

theorem dense_table (f : Form) (hf : f≠0) : ∀k : Fin 16,
    Signature.coordinateAction (slots f) (rawTarget f) (TetrahedralDeck.words k)=
      scalar f*rawDense (rawWeight f) (TetrahedralDeck.words k) := by
  rw [slots_exact]
  fin_cases f
  · exact False.elim (hf rfl)
  all_goals intro k; fin_cases k <;> decide +kernel

def phaseCode : Form→Fin 24 := ![3,0,23,16]
def phaseScalar : Form→Scalar := ![-imag,1,-imag*Coordinates.Models.zScale 2,1/(1+imag)]
def rawPhase (f : Form) : Mat := mat 1 0 0 (-(rawWeight f)^2)

theorem phase_table (f : Form) : rawPhase f=ms (phaseScalar f) (theta f (standard (phaseCode f))) := by
  fin_cases f <;> decide +kernel

theorem phaseScalar_nonzero (f : Form) : phaseScalar f≠0 := by fin_cases f <;> decide +kernel

noncomputable section
open Holant.Tractable Holant.Algebraic Holant.LocalDrafts.MainChain

def weight : Form→AlgebraicComplex := ![1,imaginaryUnit,1,zetaEight]

theorem weight_nonzero (f : Form) : weight f≠0 := by
  have hi : imaginaryUnit ≠ 0 := by
    intro h
    exact Complex.I_ne_zero (congrArg (fun z : AlgebraicComplex => (z : ℂ)) h)
  fin_cases f <;> simp [weight,hi,zetaEight_ne_zero]

theorem weight_eighth (f : Form) : weight f^8=1 := by
  have hi : imaginaryUnit^8=1 := by
    calc
      _ = (imaginaryUnit^4)^2 := by ring
      _ = 1 := by rw [imaginaryUnit_pow_four]; norm_num
  fin_cases f <;> simp [weight,hi]

theorem embed_power (z : Scalar) (n : ℕ) : embed (z^n)=embed z^n := map_pow embedding z n

theorem weight_exact (f : Form) : embed (rawWeight f)=(weight f : ℂ) := by
  fin_cases f <;> simp [rawWeight,weight,embed_div,embed_add,embed_imag,root,embed_coeff,rootTwo,
    zetaEight,coe_imaginaryUnit,coe_sqrtTwo,embed_one]

theorem target_exact (f : Form) : complexTensor (rawTarget f)=
    GlobalCloseCompletionOctahedralTerminals.target f := by
  fin_cases f
  · change complexTensor (RankTwo.BaseTerminals.terminalShape false) = RankTwo.BaseTerminals.terminalShape false
    exact RankTwo.BaseTerminals.map_shape fieldEmbedding false
  · change complexTensor (RankTwo.BaseTerminals.terminalShape true) = RankTwo.BaseTerminals.terminalShape true
    exact RankTwo.BaseTerminals.map_shape fieldEmbedding true
  · change RingHomRealization.mapSignature fieldEmbedding
      (RankTwo.MixedEndpointBridge.mixedShape false imag) = RankTwo.MixedEndpointBridge.mixedShape false Complex.I
    rw [RankTwo.MixedEndpointBridge.map_shape]
    exact congrArg (RankTwo.MixedEndpointBridge.mixedShape false) embed_imag
  · change RingHomRealization.mapSignature fieldEmbedding
      (RankTwo.MixedEndpointBridge.mixedShape true imag) = RankTwo.MixedEndpointBridge.mixedShape true Complex.I
    rw [RankTwo.MixedEndpointBridge.map_shape]
    exact congrArg (RankTwo.MixedEndpointBridge.mixedShape true) embed_imag

theorem dense_exact (f : Form) : complexTensor (rawDense (rawWeight f))=
    RingHomRealization.mapSignature (algebraicClosure ℚ ℂ).val.toRingHom
      (Holant.EightVertex.ProductAnchor.denseTensor 1 (weight f) (fun _=>false)) := by
  funext x
  by_cases hx : Holant.weight x%2=0 <;>
    simp [complexTensor,rawDense,Holant.EightVertex.ProductAnchor.denseTensor,
    RingHomRealization.mapSignature,Holant.EightVertex.ProductAnchor.bitSign,
    embed_power,weight_exact,embed_zero,hx]

theorem action_exact (f : Form) (hf : f≠0) :
    Signature.coordinateAction (fun i=>complexMatrix (slots f i))
      (GlobalCloseCompletionOctahedralTerminals.target f)=
      embed (scalar f) • RingHomRealization.mapSignature (algebraicClosure ℚ ℂ).val.toRingHom
        (Holant.EightVertex.ProductAnchor.denseTensor 1 (weight f) (fun _=>false)) := by
  have h : Signature.coordinateAction (slots f) (rawTarget f)=
      fun x=>scalar f*rawDense (rawWeight f) x := by
    funext x
    obtain ⟨k,rfl⟩ := TetrahedralDeck.words_surjective x
    exact dense_table f hf k
  have hh := congrArg complexTensor h
  rw [complexTensor_action,target_exact,complexTensor_scale,dense_exact] at hh
  exact hh

theorem phase_member (f : Form) : Direction f
    (Matrix.map (Holant.Marked.R (-(weight f^2)))
      (algebraicClosure ℚ ℂ).val.toRingHom) := by
  have he : complexMatrix (rawPhase f)=
      Matrix.map (Holant.Marked.R (-(weight f^2)))
        (algebraicClosure ℚ ℂ).val.toRingHom := by
    ext u v
    cases u <;> cases v <;>
      simp [complexMatrix,rawPhase,mat,Holant.Marked.R,diagonalKernel,
        Matrix.map_apply,embed_neg,embed_power,weight_exact,embed_zero,embed_one]
  rw [←he,phase_table,complexMatrix_ms]
  exact Direction.smul (Direction.standard f (phaseCode f)) (embed_ne_zero (phaseScalar_nonzero f))
end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralDenseData
