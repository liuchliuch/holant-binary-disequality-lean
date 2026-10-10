import Holant.Algebraic.RationalHeight
import Holant.Algebraic.FixedFamilySize
import Holant.OneHot.StackProgram.Serialization

/-! Lower bounds from the literal input bytes. These ensure variable answer
coordinates cannot be treated as fixed or hidden constant-size data. -/
namespace Holant.Algebraic
open scoped BigOperators

theorem intAbs_le_intCode (z : ℤ) : z.natAbs≤Equiv.intEquivNat z := by
  cases z with
  | ofNat n => change n≤2*n;omega
  | negSucc n => change n+1≤2*n+1;omega

theorem rationalBitHeight_le_encoded_length (q : ℚ) :
    rationalBitHeight q≤(rationalEncoding.encode q).length := by
  change (max q.num.natAbs q.den).size≤(Computability.encodeNat (rationalCode q)).length
  rw [encodeNat_length]
  apply Nat.size_le_size
  exact max_le ((intAbs_le_intCode q.num).trans (Nat.left_le_pair _ _)) (Nat.right_le_pair _ _)

theorem coordinate_height_le_encoded_length {n : ℕ} (v : Fin n→ℚ) (i : Fin n) :
    rationalBitHeight (v i)≤((vectorEncoding n).encode v).length := by
  have hs := Finset.single_le_sum (f := fun j => 2*(rationalEncoding.encode (v j)).length+1)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hq := rationalBitHeight_le_encoded_length (v i)
  change _≤(vectorEncode n v).length
  rw [vectorEncode_length]
  omega

theorem field_coordinate_height_le_encoded_length {K : Type*} [Field K] [Algebra ℚ K]
    {n : ℕ} (F : FixedField K n) (a : K) (i : Fin n) :
    rationalBitHeight (F.decode.symm a i)≤(F.encoding.encode a).length :=
  coordinate_height_le_encoded_length (F.decode.symm a) i

theorem entry_length_le_stack_length {V : Type} (e : Computability.Encoding V Bool)
    (xs : List V) (x : V) (hx : x∈xs) :
    (e.encode x).length≤((Holant.OneHot.StackProgram.stackEncoding e).encode xs).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    have he : ((Holant.OneHot.StackProgram.stackEncoding e).encode (y::ys)).length=
        2*(e.encode y).length+2+
          ((Holant.OneHot.StackProgram.stackEncoding e).encode ys).length := by
      simp [Holant.OneHot.StackProgram.stackEncoding,Holant.Complexity.framedListEncoding,
        Holant.Complexity.framedListEncode,frame_length];omega
    rw [he]
    rcases hx with rfl|hx
    · omega
    · have h := ih hx;omega

theorem list_length_le_stack_length {V : Type} (e : Computability.Encoding V Bool)
    (xs : List V) : xs.length≤((Holant.OneHot.StackProgram.stackEncoding e).encode xs).length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    simp only [List.length_cons]
    have he : ((Holant.OneHot.StackProgram.stackEncoding e).encode (y::ys)).length=
        2*(e.encode y).length+2+
          ((Holant.OneHot.StackProgram.stackEncoding e).encode ys).length := by
      simp [Holant.OneHot.StackProgram.stackEncoding,Holant.Complexity.framedListEncoding,
        Holant.Complexity.framedListEncode,frame_length];omega
    rw [he]
    omega

end Holant.Algebraic
