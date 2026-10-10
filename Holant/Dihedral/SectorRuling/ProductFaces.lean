import Holant.Dihedral.SectorRuling.CommonSupport

/-! Literal two-factor coefficient faces of a complete original matching
product. These identities supply the Segre minor calculation in source6.8. -/
noncomputable section
namespace Holant.Dihedral.SectorRuling
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Certificates
set_option backward.isDefEq.respectTransparency false
variable {s n : ℕ}

def pairFace (p : (Fin s × Bool) ≃ Fin n) (e f : Fin s) (a b c d : Bool) (x : Fin n → Bool) : Fin n → Bool :=
  insertPair (p (e,false)) (p (e,true)) a b (insertPair (p (f,false)) (p (f,true)) c d x)

def outsideProduct (p : (Fin s × Bool) ≃ Fin n) (A : Fin s → Mat) (κ : Scalar)
    (e f : Fin s) (x : Fin n → Bool) : Scalar :=
  κ*∏ d ∈ ((Finset.univ.erase e).erase f),A d (x (p (d,false))) (x (p (d,true)))

/-- Both selected original factors are extracted without dropping any scale
or assuming a local factorization of the resulting tensor. -/
theorem product_pairFace (p : (Fin s × Bool) ≃ Fin n) (A : Fin s → Mat) (κ : Scalar)
    (e f : Fin s) (hef : e ≠ f) (a b c d : Bool) (x : Fin n → Bool) :
    MatchingContractionClosure.productValue p A κ (pairFace p e f a b c d x) =
      A e a b*A f c d*outsideProduct p A κ e f x := by
  change productValue p A κ (insertPair _ _ a b (insertPair _ _ c d x))=_
  rw [product_extract_edge]
  let y := insertPair (p (f,false)) (p (f,true)) c d x
  have hmem : f ∈ ({e}ᶜ : Finset (Fin s)) := by simp [Ne.symm hef]
  rw [←Finset.mul_prod_erase ({e}ᶜ : Finset (Fin s))
    (fun k => A k (y (p (k,false))) (y (p (k,true)))) hmem]
  have hff : p (f,false) ≠ p (f,true) := by intro h; have hh := congrArg Prod.snd (p.injective h); cases hh
  have heF : A f (y (p (f,false))) (y (p (f,true)))=A f c d := by
    dsimp only [y]
    rw [insertPair_first hff,insertPair_second]
  rw [heF]
  have hrest : (∏ k ∈ ({e}ᶜ : Finset (Fin s)).erase f,A k (y (p (k,false))) (y (p (k,true)))) =
      ∏ k ∈ ((Finset.univ.erase e).erase f),A k (x (p (k,false))) (x (p (k,true))) := by
    have hset : ({e}ᶜ : Finset (Fin s))=Finset.univ.erase e := by ext k; simp
    rw [hset]
    apply Finset.prod_congr rfl
    intro k hk
    have hkf : k ≠ f := (Finset.mem_erase.mp hk).1
    have hn (u v : Bool) : p (k,u) ≠ p (f,v) := fun h => hkf (congrArg Prod.fst (p.injective h))
    dsimp only [y]
    rw [insertPair_other (hn false false) (hn false true),insertPair_other (hn true false) (hn true true)]
  rw [hrest]
  simp only [outsideProduct]
  ring

def faceDet (q : Signature Scalar n) (p : (Fin s × Bool) ≃ Fin n) (e f : Fin s)
    (α β : Bool) (x : Fin n → Bool) : Scalar :=
  q (pairFace p e f false α false β x)*q (pairFace p e f true (!α) true (!β) x)-
    q (pairFace p e f false α true (!β) x)*q (pairFace p e f true (!α) false β x)

theorem product_faceDet_zero (p : (Fin s × Bool) ≃ Fin n) (A : Fin s → Mat) (κ : Scalar)
    (e f : Fin s) (hef : e ≠ f) (α β : Bool) (x : Fin n → Bool) :
    faceDet (MatchingContractionClosure.productValue p A κ) p e f α β x=0 := by
  simp only [faceDet,product_pairFace p A κ e f hef]
  ring

/-- The source Segre minor is the product of the two actual ordered factor
coefficient determinants and the explicitly retained complementary scalars. -/
theorem combination_faceDet (p : (Fin s × Bool) ≃ Fin n) (A₀ A₁ : Fin s → Mat) (κ₀ κ₁ a b : Scalar)
    (e f : Fin s) (hef : e ≠ f) (α β : Bool) (x : Fin n → Bool) :
    faceDet (combination a b (MatchingContractionClosure.productValue p A₀ κ₀)
      (MatchingContractionClosure.productValue p A₁ κ₁)) p e f α β x =
      a*b*outsideProduct p A₀ κ₀ e f x*outsideProduct p A₁ κ₁ e f x*
        factorDet α (A₀ e) (A₁ e)*factorDet β (A₀ f) (A₁ f) := by
  simp only [faceDet,combination,product_pairFace p A₀ κ₀ e f hef,product_pairFace p A₁ κ₁ e f hef,factorDet]
  ring

end Holant.Dihedral.SectorRuling
