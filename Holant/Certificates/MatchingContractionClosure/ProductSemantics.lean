import Holant.Certificates.MatchingContractionClosure.GroupAlgebra
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Literal arbitrary-field matching coefficient extraction. The cycle scalar
may vanish. No matching or nonzero remainder is assumed after a contraction. -/
noncomputable section
namespace Holant.Certificates.MatchingContractionClosure
open Holant

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι] {E : Type*} [Fintype E] [DecidableEq E]

def trace (A C : Binary (K := K)) : K := ∑ a : Bool, ∑ b : Bool, A a b*C a b
def fuse (C A B : Binary (K := K)) : Binary (K := K) := A*C*B

def productValue (p : (E × Bool) ≃ ι) (A : E → Binary (K := K)) (κ : K) : Tensor K ι :=
  fun x => κ * ∏ e, A e (x (p (e,false))) (x (p (e,true)))

def insertPair (u v : ι) (a b : Bool) (x : ι → Bool) : ι → Bool :=
  Function.update (Function.update x u a) v b

theorem insertPair_first {u v : ι} (huv : u ≠ v) (a b : Bool) (x : ι → Bool) :
    insertPair u v a b x u = a := by simp [insertPair,huv]

theorem insertPair_second (u v : ι) (a b : Bool) (x : ι → Bool) :
    insertPair u v a b x v = b := by simp [insertPair]

theorem insertPair_other {u v i : ι} (hu : i ≠ u) (hv : i ≠ v) (a b : Bool) (x : ι → Bool) :
    insertPair u v a b x i = x i := by simp [insertPair,hu,hv]

private theorem distinct_ports (p : (E × Bool) ≃ ι) (e : E) :
    p (e,false) ≠ p (e,true) := by
  intro he
  have hh := congrArg Prod.snd (p.injective he)
  cases hh

private theorem other_edge_port (p : (E × Bool) ≃ ι) {e d : E} (h : d ≠ e) (a b : Bool) :
    p (d,a) ≠ p (e,b) := fun hh => h (congrArg Prod.fst (p.injective hh))

/-- Literal factor on an original edge and the unchanged product on all other
edges. The displayed local slice is derived from the complete tensor product. -/
theorem product_extract_edge (p : (E × Bool) ≃ ι) (A : E → Binary (K := K)) (κ : K)
    (e : E) (a b : Bool) (x : ι → Bool) :
    productValue p A κ (insertPair (p (e,false)) (p (e,true)) a b x) =
      A e a b * (κ * ∏ d ∈ {e}ᶜ, A d (x (p (d,false))) (x (p (d,true)))) := by
  rw [productValue,Fintype.prod_eq_mul_prod_compl e]
  rw [insertPair_first (distinct_ports p e),insertPair_second]
  have hh : (∏ d ∈ {e}ᶜ,
      A d (insertPair (p (e,false)) (p (e,true)) a b x (p (d,false)))
        (insertPair (p (e,false)) (p (e,true)) a b x (p (d,true)))) =
      ∏ d ∈ {e}ᶜ, A d (x (p (d,false))) (x (p (d,true))) := by
    apply Finset.prod_congr rfl
    intro d hd
    have hde : d ≠ e := by simpa using hd
    rw [insertPair_other (other_edge_port p hde false false) (other_edge_port p hde false true),
      insertPair_other (other_edge_port p hde true false) (other_edge_port p hde true true)]
  rw [hh]
  ring

/-- A source closure of any actual matching edge is exactly its trace times
the complete residual product, in the original surviving coordinates. -/
theorem close_product_edge (p : (E × Bool) ≃ ι) (A : E → Binary (K := K)) (κ : K)
    (e : E) (C : Binary (K := K)) (x : ι → Bool) :
    (∑ a : Bool, ∑ b : Bool, C a b *
      productValue p A κ (insertPair (p (e,false)) (p (e,true)) a b x)) =
      trace (A e) C * (κ * ∏ d ∈ {e}ᶜ, A d (x (p (d,false))) (x (p (d,true)))) := by
  simp only [product_extract_edge,trace,Fintype.sum_bool]
  ring

/-- Cutting one endpoint from each of two distinct original factors derives
exactly the local cross-product, with all other factors unchanged. -/
theorem product_extract_two (p : (E × Bool) ≃ ι) (A : E → Binary (K := K)) (κ : K)
    (e f : E) (hef : e ≠ f) (a b : Bool) (x : ι → Bool) :
    productValue p A κ (insertPair (p (e,true)) (p (f,false)) a b x) =
      A e (x (p (e,false))) a * A f b (x (p (f,true))) *
        (κ * ∏ d ∈ (Finset.univ.erase e).erase f, A d (x (p (d,false))) (x (p (d,true)))) := by
  let y := insertPair (p (e,true)) (p (f,false)) a b x
  let v := fun d => A d (y (p (d,false))) (y (p (d,true)))
  have hp : (∏ d, v d) = v e * (v f * ∏ d ∈ (Finset.univ.erase e).erase f, v d) := by
    rw [← Finset.mul_prod_erase Finset.univ v (Finset.mem_univ e)]
    rw [← Finset.mul_prod_erase (Finset.univ.erase e) v (by simp [Ne.symm hef] : f ∈ Finset.univ.erase e)]
  have he : v e = A e (x (p (e,false))) a := by
    dsimp [v,y]
    rw [insertPair_other (distinct_ports p e) (other_edge_port p hef false false),
      insertPair_first (other_edge_port p hef true false)]
  have hf : v f = A f b (x (p (f,true))) := by
    dsimp [v,y]
    rw [insertPair_second,insertPair_other (other_edge_port p (Ne.symm hef) true true)
      (Ne.symm (distinct_ports p f))]
  have hr : (∏ d ∈ (Finset.univ.erase e).erase f, v d) =
      ∏ d ∈ (Finset.univ.erase e).erase f, A d (x (p (d,false))) (x (p (d,true))) := by
    apply Finset.prod_congr rfl
    intro d hd
    have hde : d ≠ e := (Finset.mem_erase.mp (Finset.mem_erase.mp hd).2).1
    have hdf : d ≠ f := (Finset.mem_erase.mp hd).1
    dsimp [v,y]
    rw [insertPair_other (other_edge_port p hde false true) (other_edge_port p hdf false false),
      insertPair_other (other_edge_port p hde true true) (other_edge_port p hdf true false)]
  change κ * (∏ d, v d) = _
  rw [hp,he,hf,hr]
  ring

/-- The full matching-product contraction is the actual fused kernel times
its untouched residual product. Thus the local cross form is a conclusion. -/
theorem close_product_two (p : (E × Bool) ≃ ι) (A : E → Binary (K := K)) (κ : K)
    (e f : E) (hef : e ≠ f) (C : Binary (K := K)) (x : ι → Bool) :
    (∑ a : Bool, ∑ b : Bool, C a b *
      productValue p A κ (insertPair (p (e,true)) (p (f,false)) a b x)) =
      fuse C (A e) (A f) (x (p (e,false))) (x (p (f,true))) *
        (κ * ∏ d ∈ (Finset.univ.erase e).erase f, A d (x (p (d,false))) (x (p (d,true)))) := by
  simp only [product_extract_two p A κ e f hef,fuse,Matrix.mul_apply,Fintype.sum_bool]
  ring

/-- Arbitrary physical edge orientations can be changed while retaining the
exact original product by transposing just those literal binary tables. -/
def flipSlots (σ : E → Bool) : Equiv.Perm (E × Bool) where
  toFun q := (q.1,q.2 ^^ σ q.1)
  invFun q := (q.1,q.2 ^^ σ q.1)
  left_inv q := by rcases q with ⟨e,b⟩; simp
  right_inv q := by rcases q with ⟨e,b⟩; simp

theorem reorient_product (p : (E × Bool) ≃ ι) (A : E → Binary (K := K)) (κ : K) (σ : E → Bool) :
    productValue ((flipSlots σ).trans p) (fun e => if σ e then (A e).transpose else A e) κ =
      productValue p A κ := by
  funext x
  apply congrArg (κ * ·)
  apply Finset.prod_congr rfl
  intro e _
  cases hs : σ e <;> simp [productValue,flipSlots,hs,Matrix.transpose_apply]

end Holant.Certificates.MatchingContractionClosure
