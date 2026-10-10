import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralEndpointShapes
import Holant.Certificates.EqualityQuaternary.MonomialSource
import Holant.ReedMuller.WeightTwoIntegration.ExceptionalReconstruction

/-! Coefficient extraction from the preserved marked-octahedral proof. Literal normalized BASE certificates only. The dd
matrix is the actual W0, and the tt matrices are the four manuscript Li.
The tt coefficient operator is analytic reconstruction, never a gadget.
The advertised eight-vertex table is the OLD RankTwo.printedNine. -/
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.BaseTerminals
open Holant Holant.Algebraic Holant.Certificates
open Holant.LocalDrafts.MainChain
open Holant.Certificates.OctahedralSeparator
open scoped BigOperators Matrix

def baseForm (b : Bool) : Form := if b then 1 else 0
def baseCodes (b : Bool) : Fin 4 → Fin 24 :=
  if b then ![14,9,9,8] else fun _ => 20
def baseReverse : Fin 4 → Bool := fun _ => false
def paletteLegs (b : Bool) (i : Fin 4) : Mat :=
  theta (baseForm b) (OctahedralSeparator.standard (baseCodes b i))

def halfParity : Signature Scalar 4 := fun x =>
  if Holant.Marked.SupportAtlas.parity x then 0 else rat (1/2)
def W0 : Mat := mat 1 1 1 (-1)

/-- H here describes coefficients on the original four ordered ports.
Only paletteLegs, never these analytic matrices, are physically attached. -/
def coefficientPorts (f : Form) : Fin 4 → Mat :=
  ![mt (conjugator f),inverseConjugator f,inverseConjugator f,
    mm (mm flip (mt (conjugator f))) flip]
def baseTensor (b : Bool) : Signature Scalar 4 :=
  if b then Signature.coordinateAction (coefficientPorts 1) halfParity else halfParity
def actualLi : Fin 4 → Mat :=
  ![theta 1 (OctahedralSeparator.standard 14),
    theta 1 (OctahedralSeparator.standard 9),
    theta 1 (OctahedralSeparator.standard 9),
    mm flip (theta 1 (OctahedralSeparator.standard 23))]

def terminalTensor (b : Bool) : Signature Scalar 4 :=
  if b then RankTwo.printedNine else RankTwo.literalEquality
def terminalScale (b : Bool) : Scalar := if b then -4*root else 4
def fourthScale : Scalar := coeff 0 0 0 (1/2)
def liScales (i : Fin 4) : Scalar := if i = 3 then fourthScale else 1

/-- Same old four-word equivalence; only its coefficient codomain changes. -/
private theorem scalar_sum_four (f : Word → Scalar) :
    (∑ x,f x) = ∑ a : Bool,∑ b : Bool,∑ c : Bool,∑ d : Bool,f ![a,b,c,d] := by
  simp only [Holant.ReedMuller.CoefficientAtlas.sum_words_succ,Fintype.sum_unique]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  congr 1

/-- Factor the actual sixteen-term sum before checking the fixed table. -/
theorem halfParity_action (A : Fin 4 → Mat) (x : Word) :
    Signature.coordinateAction A halfParity x = (1/4 : Scalar)*
      ((∏ i,(A i (x i) false+A i (x i) true))+
        (∏ i,(A i (x i) false-A i (x i) true))) := by
  have hhalf : rat (1/2) = (1/2 : Scalar) := by decide +kernel
  unfold halfParity
  simp only [hhalf]
  simp only [Signature.coordinateAction,scalar_sum_four]
  simp [Holant.Marked.SupportAtlas.parity,Fin.prod_univ_succ]
  ring

theorem W0_standard : W0 = ms (-imag) (theta 0 (OctahedralSeparator.standard 20)) := by
  decide +kernel

theorem dd_palette : paletteLegs false = fun _ => imag • W0 := by
  funext i
  change theta 0 (OctahedralSeparator.standard 20) = imag • W0
  decide +kernel

/-- Undo the OLD anchorU's literal output diagonal, including its factor 2.
This is proof-coordinate algebra, not a newly installed physical matrix. -/
private def anchorUndo : Kernel ℂ := fun a b =>
  if a = b then if a then -2*Complex.I else 2 else 0

private theorem W0_complex : complexMatrix W0 = Holant.ReedMuller.CoefficientAtlas.walshKernel := by
  ext a b
  cases a <;> cases b <;>
    change embedding _ = _ <;>
    norm_num [W0,mat,Holant.ReedMuller.CoefficientAtlas.walshKernel]

private theorem undo_anchor : Kernel.mul anchorUndo
    Holant.ReedMuller.WeightTwoIntegration.anchorU = complexMatrix W0 := by
  rw [W0_complex]
  funext a b
  cases a <;> cases b <;>
    norm_num [Kernel.mul_apply,anchorUndo,Holant.ReedMuller.WeightTwoIntegration.anchorU,
      Holant.ReedMuller.CoefficientAtlas.walshKernel,Complex.I_sq] <;>
    ring_nf <;> norm_num [Complex.I_sq]

private theorem halfParity_complex : complexTensor halfParity = fun x =>
    (1/2 : ℂ)*Holant.ReedMuller.WeightTwoIntegration.even4 x := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    norm_num [complexTensor,halfParity,Holant.Marked.SupportAtlas.parity,
      Holant.ReedMuller.WeightTwoIntegration.even4,h0,h1,h2,h3,rat,embed_coeff,embed_zero]

private theorem eq4_complex : complexTensor RankTwo.literalEquality =
    Holant.ReedMuller.WeightTwoIntegration.eq4 := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [complexTensor,RankTwo.literalEquality,Holant.ReedMuller.WeightTwoIntegration.eq4,
      funext_iff,Fin.forall_fin_succ,h0,h1,h2,h3,embed_one,embed_zero]

private theorem undo_equality : Signature.coordinateAction (fun _ => anchorUndo)
    Holant.ReedMuller.WeightTwoIntegration.eq4 =
      fun x => (16 : ℂ)*Holant.ReedMuller.WeightTwoIntegration.eq4 x := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    norm_num [Signature.coordinateAction,RankTwo.PhysicalOrbit.sum_four,anchorUndo,
      Holant.ReedMuller.WeightTwoIntegration.eq4,Fin.prod_univ_succ,
      Fin.forall_fin_succ,h0,h1,h2,h3,Complex.I_sq] <;>
    ring_nf <;> norm_num [Complex.I_sq]

/-- Consume the already proved anchor_even4 substitution. Only the actual
diagonal cancellation is new; the Walsh coefficient sum is not reproved. -/
private theorem dd_complex_exact :
    Signature.coordinateAction (fun _ => complexMatrix W0) (complexTensor halfParity) =
      fun x => (4 : ℂ)*Holant.ReedMuller.WeightTwoIntegration.eq4 x := by
  have hanchor : Signature.coordinateAction
      (fun _ => Holant.ReedMuller.WeightTwoIntegration.anchorU) (complexTensor halfParity) =
        fun x => (1/4 : ℂ)*Holant.ReedMuller.WeightTwoIntegration.eq4 x := by
    rw [halfParity_complex,Holant.ReedMuller.WeightTwoIntegration.coordinateAction_scalar,
      Holant.ReedMuller.WeightTwoIntegration.anchor_even4]
    funext x
    ring
  have hcomp := Signature.coordinateAction_comp (fun _ : Fin 4 => anchorUndo)
    (fun _ => Holant.ReedMuller.WeightTwoIntegration.anchorU) (complexTensor halfParity)
  simp only [undo_anchor] at hcomp
  rw [← hcomp,hanchor,Holant.ReedMuller.WeightTwoIntegration.coordinateAction_scalar,undo_equality]
  funext x
  ring

theorem dd_exact : Signature.coordinateAction (fun _ => W0) halfParity =
    tensorScale 4 RankTwo.literalEquality := by
  apply complexTensor_injective
  have hfour : embed (4 : Scalar) = (4 : ℂ) := by
    exact map_natCast embedding 4
  have hs := complexTensor_scale (4 : Scalar) (RankTwo.literalEquality : Signature Scalar 4)
  rw [hfour,eq4_complex] at hs
  exact (complexTensor_action _ _).trans (dd_complex_exact.trans hs.symm)

theorem dd_table (k : Fin 16) :
    Signature.coordinateAction (fun _ => W0) halfParity (TetrahedralDeck.words k) =
      tensorScale 4 RankTwo.literalEquality (TetrahedralDeck.words k) :=
  congrFun dd_exact (TetrahedralDeck.words k)

/-- Literal Li4 = (i sqrt2/2) theta_1(standard 8). The left X is retained. -/
theorem li_palette : ∀ i : Fin 4,actualLi i = liScales i • paletteLegs true i := by
  intro i
  fin_cases i <;> decide +kernel

theorem fourthScale_ne : fourthScale ≠ 0 := by decide +kernel
theorem liScales_ne (i : Fin 4) : liScales i ≠ 0 := by
  by_cases hi : i = 3
  · simpa only [liScales,if_pos hi] using fourthScale_ne
  · simpa only [liScales,if_neg hi] using (one_ne_zero : (1 : Scalar) ≠ 0)
theorem liScales_product : (∏ i,liScales i) = fourthScale := by
  simp [liScales,Fin.prod_univ_succ]

/-- Products Li Ti on the SAME four positions. These small exact entries
avoid reevaluating the analytic tensor inside every coefficient check. -/
def combinedLi : Fin 4 → Mat :=
  ![mat (coeff 1 1 (-1) 0) (coeff 1 (-1) (-1) 0)
      (coeff 1 0 1 (-1)) (coeff 1 0 1 1),
    mat (coeff 0 (1/4) (-1/2) (-1/4)) (coeff 0 (1/4) (1/2) (-1/4))
      (coeff (-1/2) (1/4) 0 (1/4)) (coeff (1/2) (1/4) 0 (1/4)),
    mat (coeff 0 (1/4) (-1/2) (-1/4)) (coeff 0 (1/4) (1/2) (-1/4))
      (coeff (-1/2) (1/4) 0 (1/4)) (coeff (1/2) (1/4) 0 (1/4)),
    mat (coeff 1 0 1 1) (coeff 1 0 1 (-1))
      (coeff (-1) 1 1 0) (coeff (-1) (-1) 1 0)]

theorem combinedLi_exact : ∀ i : Fin 4,
    mm (actualLi i) (coefficientPorts 1 i) = combinedLi i := by
  intro i
  fin_cases i <;> funext u v <;> cases u <;> cases v <;> decide +kernel

theorem combinedLi_table : ∀ k : Fin 16,
    Signature.coordinateAction combinedLi halfParity (TetrahedralDeck.words k) =
      tensorScale (-4*imag) RankTwo.printedNine (TetrahedralDeck.words k) := by
  intro k
  rw [halfParity_action]
  fin_cases k <;> decide +kernel

theorem tt_Li_exact : Signature.coordinateAction actualLi (baseTensor true) =
    tensorScale (-4*imag) RankTwo.printedNine := by
  simp only [baseTensor,ite_true]
  rw [Signature.coordinateAction_comp]
  have hc : (fun i => Kernel.mul (actualLi i) (coefficientPorts 1 i)) = combinedLi := by
    funext i u v
    rw [Kernel.mul_apply]
    exact congrFun (congrFun (combinedLi_exact i) u) v
  rw [hc]
  funext x
  obtain ⟨k,rfl⟩ := TetrahedralDeck.words_surjective x
  exact combinedLi_table k

theorem li_action (R : Signature Scalar 4) :
    Signature.coordinateAction actualLi R =
      fourthScale • Signature.coordinateAction (paletteLegs true) R := by
  have hl : actualLi = fun i => liScales i • paletteLegs true i := funext li_palette
  rw [hl,RankTwo.PhysicalOrbit.action_slot_scalars,liScales_product]

theorem palette_exact (b : Bool) :
    Signature.coordinateAction (paletteLegs b) (baseTensor b) =
      terminalScale b • terminalTensor b := by
  cases b with
  | false =>
      rw [dd_palette,RankTwo.PhysicalOrbit.action_slot_scalars]
      have hi : (∏ _ : Fin 4,imag) = (1 : Scalar) := by decide +kernel
      rw [hi,one_smul]
      exact dd_exact
  | true =>
      have h : fourthScale • Signature.coordinateAction (paletteLegs true) (baseTensor true) =
          tensorScale (-4*imag) RankTwo.printedNine :=
        (li_action (baseTensor true)).symm.trans tt_Li_exact
      have hs : fourthScale⁻¹*(-4*imag) = -4*root := by decide +kernel
      calc
        Signature.coordinateAction (paletteLegs true) (baseTensor true) =
            fourthScale⁻¹ • (fourthScale •
              Signature.coordinateAction (paletteLegs true) (baseTensor true)) := by
                rw [smul_smul,inv_mul_cancel₀ fourthScale_ne,one_smul]
        _ = fourthScale⁻¹ • tensorScale (-4*imag) RankTwo.printedNine := by rw [h]
        _ = terminalScale true • terminalTensor true := by
          funext x
          change fourthScale⁻¹*((-4*imag)*RankTwo.printedNine x)=(-4*root)*RankTwo.printedNine x
          rw [←mul_assoc,hs]

theorem terminalScale_ne (b : Bool) : terminalScale b ≠ 0 := by
  cases b <;> decide +kernel

/-- Old printed table 9, with its entries restored as literal 0,+1,-1
in any original field; no new eight-vertex table is chosen. -/
def terminalShape {K : Type*} [Field K] (b : Bool) : Signature K 4 := fun x =>
  if b then
    if Holant.Marked.SupportAtlas.parity x then 0 else
      if x = (fun _ => false) ∨ x = (fun _ => true) then 1 else -1
  else RankTwo.literalEquality x

theorem terminalTensor_shape (b : Bool) : terminalTensor b = terminalShape b := by
  cases b with
  | false => rfl
  | true =>
      funext x
      obtain ⟨k,rfl⟩ := TetrahedralDeck.words_surjective x
      fin_cases k <;> decide +kernel

theorem shape_zero {K : Type*} [Field K] (b : Bool) :
    terminalShape (K := K) b (fun _ => false) = 1 := by
  cases b <;> simp [terminalShape,RankTwo.literalEquality,Holant.Marked.SupportAtlas.parity]
theorem shape_one {K : Type*} [Field K] (b : Bool) :
    terminalShape (K := K) b (fun _ => true) = 1 := by
  cases b <;> simp [terminalShape,RankTwo.literalEquality,Holant.Marked.SupportAtlas.parity]
theorem shape_odd {K : Type*} [Field K] (b : Bool) (x : Word)
    (hx : Holant.weight x % 2 = 1) : terminalShape (K := K) b x = 0 := by
  cases b with
  | false => exact (RankTwo.equality_endpoint (RankTwo.literalEquality : Signature K 4)
      ⟨by simp [RankTwo.literalEquality],fun x => by simp [RankTwo.literalEquality]⟩).2.2 x hx
  | true =>
      simp [terminalShape,(EqualityQuaternary.parity_weight x).mpr hx]

noncomputable section
def complexBase (b : Bool) : Signature ℂ 4 := complexTensor (baseTensor b)
def complexTerminal (b : Bool) : Signature ℂ 4 := complexTensor (terminalTensor b)
def complexScale (b : Bool) : ℂ := embed (terminalScale b)
def complexLegs (b : Bool) (i : Fin 4) : Matrix Bool Bool ℂ := complexMatrix (paletteLegs b i)

theorem complex_exact (b : Bool) :
    Signature.coordinateAction (complexLegs b) (complexBase b) =
      complexScale b • complexTerminal b := by
  change Signature.coordinateAction (fun i => complexMatrix (paletteLegs b i))
    (complexTensor (baseTensor b)) = embed (terminalScale b) • complexTensor (terminalTensor b)
  rw [← complexTensor_action,palette_exact]
  exact complexTensor_scale _ _

theorem complexScale_ne (b : Bool) : complexScale b ≠ 0 :=
  embed_ne_zero (terminalScale_ne b)

theorem complexLegs_direction (b : Bool) (i : Fin 4) :
    Direction (baseForm b) (complexLegs b i) := Direction.standard _ _

theorem W0_direction : Direction 0 (complexMatrix W0) := by
  rw [W0_standard,complexMatrix_ms]
  exact (Direction.standard 0 20).smul (embed_ne_zero (by decide +kernel : -imag ≠ 0))

theorem actualLi_direction (i : Fin 4) : Direction 1 (complexMatrix (actualLi i)) := by
  have he : actualLi i = ms (liScales i) (paletteLegs true i) := li_palette i
  rw [he,complexMatrix_ms]
  exact (complexLegs_direction true i).smul (embed_ne_zero (liScales_ne i))

theorem map_shape {K M : Type*} [Field K] [Field M] (ρ : K →+* M) (b : Bool) :
    RingHomRealization.mapSignature ρ (terminalShape (K := K) b) = terminalShape b := by
  funext x
  cases b <;> simp only [RingHomRealization.mapSignature,terminalShape,RankTwo.literalEquality,
    Bool.false_eq_true,ite_false,ite_true]
  all_goals split_ifs <;> simp

theorem complexTerminal_shape (b : Bool) : complexTerminal b = terminalShape b := by
  rw [complexTerminal,terminalTensor_shape]
  exact map_shape fieldEmbedding b

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.BaseTerminals
