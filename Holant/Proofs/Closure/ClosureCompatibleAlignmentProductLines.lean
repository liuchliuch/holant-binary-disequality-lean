import Holant.Proofs.Closure.ClosureMatchingResidual

/-! Equal nonzero whole coefficient tensors determine the line of every
literal common matching factor.  A matching ancestor's pair contractions
also have an internally constructed common product in which at most one
matrix depends on the selected kernel, including all zero cycle scalars. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
open Holant Holant.Certificates.MatchingContractionClosure

variable {K P E : Type} [Field K] [DecidableEq P] [Fintype E] [DecidableEq E]

theorem equal_products_factor_line (p : (E × Bool) ≃ P)
    (A B : E → Binary (K:=K)) (c d : K)
    (nonzero : productValue p A c ≠ 0) (same : productValue p A c = productValue p B d)
    (e : E) : ∃ z : K,z ≠ 0 ∧ B e = z • A e := by
  classical
  obtain ⟨x,hx⟩ : ∃ x,productValue p A c x ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact nonzero (funext hn)
  have inserted : insertPair (p (e,false)) (p (e,true))
      (x (p (e,false))) (x (p (e,true))) x = x := by simp [insertPair]
  let a := c * ∏ j ∈ {e}ᶜ,A j (x (p (j,false))) (x (p (j,true)))
  let b := d * ∏ j ∈ {e}ᶜ,B j (x (p (j,false))) (x (p (j,true)))
  have extractA := product_extract_edge p A c e (x (p (e,false))) (x (p (e,true))) x
  have extractB := product_extract_edge p B d e (x (p (e,false))) (x (p (e,true))) x
  rw [inserted] at extractA extractB
  have ha : a ≠ 0 := by
    intro zero
    apply hx
    rw [extractA]
    change A e (x (p (e,false))) (x (p (e,true))) * a = 0
    rw [zero,mul_zero]
  have hb : b ≠ 0 := by
    intro zero
    apply hx
    rw [same,extractB]
    change B e (x (p (e,false))) (x (p (e,true))) * b = 0
    rw [zero,mul_zero]
  refine ⟨a/b,div_ne_zero ha hb,?_⟩
  funext u v
  have h := congrFun same (insertPair (p (e,false)) (p (e,true)) u v x)
  rw [product_extract_edge,product_extract_edge] at h
  change A e u v*a = B e u v*b at h
  change B e u v = (a/b)*A e u v
  field_simp [hb]
  linear_combination -h

structure OneVariableProducts (u v : P) (f : Tensor K P) where
  products : ClosureMatchingResidual.Products u v f
  exceptional : Option products.Edge
  fixed : ∀ C₀ C₁ j, some j ≠ exceptional → products.matrix C₀ j = products.matrix C₁ j

/-- The residual port bijection and exceptional edge come from the actual
same-edge/cross-edge incidence of the original matching.  No selected output
presentation or desired common-factor witness is a constructor input. -/
theorem oneVariableProducts_nonempty (M : Presentation K P) (u v : P) (distinct : u ≠ v) :
    Nonempty (OneVariableProducts u v M.tensor) := by
  classical
  let p := M.ports
  let A := M.matrix
  let e := (p.symm u).1
  let d := (p.symm v).1
  by_cases same : e = d
  · let sigma := sameMask p u
    let p' := (flipSlots sigma).trans p
    let A' := orientedFactors A sigma
    have original : productValue p' A' M.scalar = M.tensor := reorient_product p A M.scalar sigma
    obtain ⟨hu,hv⟩ := same_selected_ports p u v distinct same
    change p' (e,false) = u at hu
    change p' (e,true) = v at hv
    have result : Nonempty (OneVariableProducts (p' (e,false)) (p' (e,true)) (productValue p' A' M.scalar)) := by
      refine ⟨{
        products := {
          Edge := OtherEdges e
          finite := inferInstance
          decidable := inferInstance
          ports := deletePorts p' e
          matrix := fun _ j => A' j.val
          scalar := fun C => trace (A' e) C*M.scalar
          equation := fun C => contract_matched p' A' M.scalar e C }
        exceptional := none
        fixed := fun _ _ _ _ => rfl }⟩
    simpa only [hu,hv,original] using result
  · let sigma := crossMask p u v
    let p' := (flipSlots sigma).trans p
    let A' := orientedFactors A sigma
    have original : productValue p' A' M.scalar = M.tensor := reorient_product p A M.scalar sigma
    obtain ⟨hu,hv⟩ := cross_selected_ports p u v same
    change p' (e,true) = u at hu
    change p' (d,false) = v at hv
    have result : Nonempty (OneVariableProducts (p' (e,true)) (p' (d,false)) (productValue p' A' M.scalar)) := by
      refine ⟨{
        products := {
          Edge := OtherEdges d
          finite := inferInstance
          decidable := inferInstance
          ports := splicePorts p' e d
          matrix := fun C => spliceFactors C A' e d
          scalar := fun _ => M.scalar
          equation := fun C => contract_cross p' A' M.scalar e d same C }
        exceptional := some ⟨e,same⟩
        fixed := ?_ }⟩
      intro C₀ C₁ j different
      have he : j.val ≠ e := by
        intro equal
        apply different
        congr 1
        exact Subtype.ext equal
      simp only [spliceFactors,he,ite_false]
    simpa only [hu,hv,original] using result

def oneVariableProducts (M : Presentation K P) (u v : P) (distinct : u ≠ v) :
    OneVariableProducts u v M.tensor := Classical.choice (oneVariableProducts_nonempty M u v distinct)

/-- On every nonexceptional ACTUAL residual edge, equal whole tensors force
the two displayed output factors to agree projectively.  In particular the
global cycle scalar may differ, and it is never silently dropped. -/
theorem OneVariableProducts.fixed_factor_lines {u v : P} {f : Tensor K P}
    (R : OneVariableProducts u v f) (C₀ C₁ : Binary (K:=K))
    (A₀ A₁ : R.products.Edge → Binary (K:=K)) (c₀ c₁ : K)
    (nonzero₀ : contractPair u v C₀ f ≠ 0) (nonzero₁ : contractPair u v C₁ f ≠ 0)
    (equation₀ : contractPair u v C₀ f = productValue R.products.ports A₀ c₀)
    (equation₁ : contractPair u v C₁ f = productValue R.products.ports A₁ c₁)
    (j : R.products.Edge) (fixed : some j ≠ R.exceptional) :
    ∃ z : K,z ≠ 0 ∧ A₁ j = z • A₀ j := by
  have source₀ : productValue R.products.ports (R.products.matrix C₀) (R.products.scalar C₀) ≠ 0 :=
    fun zero => nonzero₀ ((R.products.equation C₀).trans zero)
  have source₁ : productValue R.products.ports (R.products.matrix C₁) (R.products.scalar C₁) ≠ 0 :=
    fun zero => nonzero₁ ((R.products.equation C₁).trans zero)
  obtain ⟨z₀,hz₀,line₀⟩ := equal_products_factor_line R.products.ports _ A₀ _ c₀ source₀
    ((R.products.equation C₀).symm.trans equation₀) j
  obtain ⟨z₁,hz₁,line₁⟩ := equal_products_factor_line R.products.ports _ A₁ _ c₁ source₁
    ((R.products.equation C₁).symm.trans equation₁) j
  refine ⟨z₁/z₀,div_ne_zero hz₁ hz₀,?_⟩
  rw [line₀,line₁,R.fixed C₀ C₁ j fixed,smul_smul,div_mul_cancel₀ z₁ hz₀]

/-- Two genuine coefficient/parity line disagreements cannot both come from
a matching ancestor in the internally constructed common residual order. -/
theorem OneVariableProducts.no_two_discrepancies {u v : P} {f : Tensor K P}
    (R : OneVariableProducts u v f) (C₀ C₁ : Binary (K:=K))
    (A₀ A₁ : R.products.Edge → Binary (K:=K)) (c₀ c₁ : K)
    (nonzero₀ : contractPair u v C₀ f ≠ 0) (nonzero₁ : contractPair u v C₁ f ≠ 0)
    (equation₀ : contractPair u v C₀ f = productValue R.products.ports A₀ c₀)
    (equation₁ : contractPair u v C₁ f = productValue R.products.ports A₁ c₁)
    (j k : R.products.Edge) (distinct : j ≠ k)
    (tagj : ¬ ∃ z : K,z ≠ 0 ∧ A₁ j = z • A₀ j)
    (tagk : ¬ ∃ z : K,z ≠ 0 ∧ A₁ k = z • A₀ k) : False := by
  classical
  by_cases hj : some j ≠ R.exceptional
  · exact tagj (R.fixed_factor_lines C₀ C₁ A₀ A₁ c₀ c₁ nonzero₀ nonzero₁ equation₀ equation₁ j hj)
  · have hk : some k ≠ R.exceptional := by
      intro same
      have he : some j = R.exceptional := not_ne_iff.mp hj
      exact distinct (Option.some.inj (he.trans same.symm))
    exact tagk (R.fixed_factor_lines C₀ C₁ A₀ A₁ c₀ c₁ nonzero₀ nonzero₁ equation₀ equation₁ k hk)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
