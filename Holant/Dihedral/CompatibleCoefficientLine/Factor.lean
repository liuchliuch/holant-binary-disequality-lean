import Holant.Dihedral.CompatibleCoefficientLine.Basic

/-! Four literal sampled cards recover all four original slices. Their exact
common binary factor is analytic and is never asserted to be a gadget resource. -/
noncomputable section
namespace Holant.Dihedral.CompatibleCoefficientLine
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure

abbrev Sample := Bool × Bool

def phase (t₀ t₁ : Scalar) (i : Sample) : Scalar := if i.2 then t₁ else t₀

theorem pair_eta {n : ℕ} (x : Fin (n+2) → Bool) : pair (x 0) (x 1) (tail x) = x := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> rfl

/-- The four inverses in the source, in the order A,D,C,B. -/
def inverseSlices {n : ℕ} (t₀ t₁ : Scalar) (H : Sample → Signature Scalar n) : Signature Scalar (n+2) :=
  fun x => if x 0 then
    if x 1 then (H (false,true) (tail x) - H (false,false) (tail x))/(t₁-t₀)
    else (H (true,true) (tail x) - H (true,false) (tail x))/(t₁-t₀)
  else if x 1 then (t₁*H (true,false) (tail x)-t₀*H (true,true) (tail x))/(t₁-t₀)
    else (t₁*H (false,false) (tail x)-t₀*H (false,true) (tail x))/(t₁-t₀)

/-- Exact four-card inversion, including cards that vanish on individual words.
The ancestor itself and its complementary factor may have arbitrary zeros. -/
theorem four_card_inversion {n : ℕ} (t₀ t₁ : Scalar) (ht : t₀ ≠ t₁)
    (f : Signature Scalar (n+4)) (B : Mat) (H : Sample → Signature Scalar n)
    (hcard : ∀ i a b x, close i.1 (phase t₀ t₁ i) f (pair a b x) = B a b * H i x) :
    ∀ a b c d x, f (pair a b (pair c d x)) = B c d * inverseSlices t₀ t₁ H (pair a b x) := by
  intro a b c d x
  have h00 := hcard (false,false) c d x
  have h01 := hcard (false,true) c d x
  have h10 := hcard (true,false) c d x
  have h11 := hcard (true,true) c d x
  simp only [close,phase,M,monomial,Fintype.sum_bool,Bool.false_xor,Bool.true_xor,
    Bool.not_false,Bool.not_true,ite_true,ite_false,Bool.false_eq_true,reduceCtorEq,
    one_mul,zero_mul,mul_zero,add_zero,zero_add] at h00 h01 h10 h11
  have hd : t₁-t₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  have hi : inverseSlices t₀ t₁ H (pair a b x) =
      if a then (if b then (H (false,true) x-H (false,false) x)/(t₁-t₀)
        else (H (true,true) x-H (true,false) x)/(t₁-t₀))
      else (if b then (t₁*H (true,false) x-t₀*H (true,true) x)/(t₁-t₀)
        else (t₁*H (false,false) x-t₀*H (false,true) x)/(t₁-t₀)) := rfl
  rw [hi]
  cases a <;> cases b <;> simp only [Bool.false_eq_true,reduceCtorEq,ite_true,ite_false] <;> field_simp [hd]
  · linear_combination t₁*h00-t₀*h01
  · linear_combination t₁*h10-t₀*h11
  · linear_combination h11-h10
  · linear_combination h01-h00

/-- Four actual full matching products with one common ordered original edge.
Their scalar normalizations are kept, and all other matchings may differ. -/
structure FourProducts {n r : ℕ} (F : SignatureFamily Scalar)
    (t₀ t₁ : Scalar) (f : Signature Scalar (n+4)) where
  ports : Sample → (Fin r × Bool) ≃ Fin (n+2)
  factors : Sample → Fin r → Mat
  edge : Sample → Fin r
  first : ∀ i, ports i (edge i,false) = 0
  second : ∀ i, ports i (edge i,true) = 1
  scalar : Sample → Scalar
  scalar_ne_zero : ∀ i, scalar i ≠ 0
  normalization : Sample → Scalar
  normalization_ne_zero : ∀ i, normalization i ≠ 0
  actual : ∀ i, Gadget.Realizes F .disequality
    (normalization i • close i.1 (phase t₀ t₁ i) f)
  equation : ∀ i, normalization i • close i.1 (phase t₀ t₁ i) f =
    productValue (ports i) (factors i) (scalar i)

def FourProducts.complement {n r : ℕ} {F : SignatureFamily Scalar} {t₀ t₁ : Scalar}
    {f : Signature Scalar (n+4)} (D : FourProducts (r:=r) F t₀ t₁ f) (i : Sample) : Signature Scalar n :=
  fun x => (D.scalar i * ∏ e ∈ ({D.edge i}ᶜ : Finset (Fin r)),
    D.factors i e (pair false false x (D.ports i (e,false)))
      (pair false false x (D.ports i (e,true)))) / D.normalization i

/-- Complement extraction is proved from the full products of actual cards. -/
theorem FourProducts.extract {n r : ℕ} {F : SignatureFamily Scalar} {t₀ t₁ : Scalar}
    {f : Signature Scalar (n+4)} (D : FourProducts (r:=r) F t₀ t₁ f)
    (i : Sample) (a b : Bool) (x : Fin n → Bool) :
    close i.1 (phase t₀ t₁ i) f (pair a b x) =
      D.factors i (D.edge i) a b * D.complement i x := by
  have he := congrFun (D.equation i) (pair a b x)
  have hi : insertPair (D.ports i (D.edge i,false)) (D.ports i (D.edge i,true)) a b
      (pair false false x) = pair a b x := by
    rw [D.first,D.second]
    funext j
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => ?_) k) j
    · simp [insertPair,pair]
    · simp [insertPair,pair]
    · simp [insertPair,pair,Fin.succ_succ_ne_one]
  rw [← hi,product_extract_edge] at he
  simp only [hi,Pi.smul_apply,smul_eq_mul] at he
  dsimp [FourProducts.complement]
  field_simp [D.normalization_ne_zero i]
  linear_combination he

/-- The source exact tensor factor, with the original p,e order displayed.
No realization claim is made for either analytic factor. -/
theorem source_genuine_factor {n r : ℕ} {F : SignatureFamily Scalar} {t₀ t₁ : Scalar}
    {f : Signature Scalar (n+4)} (D : FourProducts (r:=r) F t₀ t₁ f)
    (ht : t₀ ≠ t₁) (B : Mat) (hB : IsMonomial B)
    (hline : ∀ i, ProjectivelyEqual (D.factors i (D.edge i)) B) :
    ∃ h : Signature Scalar (n+2), IsMonomial B ∧
      ∀ a b c d x, f (pair a b (pair c d x)) = B c d * h (pair a b x) := by
  choose c hc he using hline
  let H : Sample → Signature Scalar n := fun i x => c i * D.complement i x
  refine ⟨inverseSlices t₀ t₁ H,hB,four_card_inversion t₀ t₁ ht f B H ?_⟩
  intro i a b x
  rw [D.extract,he]
  simp only [scale,H]
  ring

end Holant.Dihedral.CompatibleCoefficientLine
