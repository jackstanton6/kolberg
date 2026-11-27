import PentagonalNumber.Partition

/-!
# Kolberg's theorem on the parity of the partition function

Let `p n` be the number of partitions of `n`. In 1959 O. Kolberg proved that `p n` is even for
infinitely many `n` and odd for infinitely many `n`.

## Proof

Euler's pentagonal number theorem gives the recurrence (for `n ≥ 1`)
$$\sum_{k \in \mathbb{Z}} (-1)^k\, p\!\left(n - \tfrac{k(3k-1)}{2}\right) = 0,$$
where terms with negative argument are omitted. Reducing mod 2 removes the signs.

Suppose `p m ≡ c (mod 2)` for all `m ≥ N`. Pick a generalised pentagonal number
`G = (j+1)(3j+2)/2` with `j = N + 1`. The previous generalised pentagonal number is
`j(3j+1)/2 = G - (2j+1)`, so every other pentagonal number `g < G` satisfies
`G - g ≥ 2j + 1 > N`. Subtracting the recurrence at `G - 1` from the one at `G`, every term
cancels mod 2 (both equal `c`) except the single term `p(G - G) = p 0 = 1`, giving `1 ≡ 0`.

The pentagonal recurrence is `Nat.Partition.sum_partition` from Weiyi Wang's
`PentagonalNumber` library.
-/

open Finset

namespace Kolberg

/-- The partition function: `p n` is the number of partitions of `n`. -/
abbrev p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- The generalised pentagonal number `k(3k-1)/2` (for `k : ℤ`). -/
def pent (k : ℤ) : ℤ := k * (3 * k - 1) / 2

lemma two_mul_pent (k : ℤ) : 2 * pent k = k * (3 * k - 1) := two_pentagonal k

lemma pent_nonneg (k : ℤ) : 0 ≤ pent k := pentagonal_nonneg k

lemma pent_injective : Function.Injective pent := pentagonal_injective

lemma mem_kSet_iff {n k : ℤ} : k ∈ Nat.Partition.kSet n ↔ pent k ≤ n :=
  Nat.Partition.mem_kSet_iff

lemma pent_zero : pent 0 = 0 := by simp [pent]

lemma negOnePow_cast_zmod_two (k : ℤ) : ((k.negOnePow : ℤ) : ZMod 2) = 1 := by
  rcases Int.even_or_odd k with h | h
  · rw [Int.negOnePow_even k h]
    simp
  · rw [Int.negOnePow_odd k h]
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    decide

/-- The pentagonal recurrence for `p`, reduced mod 2. -/
theorem recurrence_mod_two (n : ℕ) (hn : n ≠ 0) :
    ∑ k ∈ Nat.Partition.kSet n, (p (n - (pent k).toNat) : ZMod 2) = 0 := by
  have h := congrArg (Int.cast : ℤ → ZMod 2) (Nat.Partition.sum_partition n hn)
  push_cast at h
  simpa [negOnePow_cast_zmod_two, pent] using h

/-- Gap lemma: the generalised pentagonal number just below `pent (j + 1) = (j+1)(3j+2)/2`
is `j(3j+1)/2`, which is smaller by `2j+1`. -/
lemma pent_gap (j : ℕ) {k₀ : ℤ} (hk₀ : k₀ = (j : ℤ) + 1) (k : ℤ) (hk : pent k < pent k₀) :
    pent k + (2 * j + 1) ≤ pent k₀ := by
  subst hk₀
  have h1 := two_mul_pent k
  have h2 := two_mul_pent ((j : ℤ) + 1)
  have hj : (0 : ℤ) ≤ j := by positivity
  have hlt : k * (3 * k - 1) < ((j : ℤ) + 1) * (3 * ((j : ℤ) + 1) - 1) := by linarith
  suffices k * (3 * k - 1) ≤ (j : ℤ) * (3 * j + 1) by nlinarith
  rcases le_or_gt ((j : ℤ) + 1) k with hk1 | hk1
  · exfalso
    have : 0 ≤ (k - ((j : ℤ) + 1)) * (3 * k + 3 * j + 2) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  rcases le_or_gt k (-((j : ℤ) + 1)) with hk2 | hk2
  · exfalso
    have ha : 0 ≤ -k - ((j : ℤ) + 1) := by linarith
    have : 0 ≤ (-k - ((j : ℤ) + 1)) * (-k - ((j : ℤ) + 1)) := mul_nonneg ha ha
    have : 0 ≤ (-k - ((j : ℤ) + 1)) * (j : ℤ) := mul_nonneg ha hj
    nlinarith
  · have : 0 ≤ ((j : ℤ) + k) * (3 * ((j : ℤ) - k) + 1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

/-- **Core lemma.** The parity of `p m` is not eventually constant. -/
theorem not_eventually_const (c : ZMod 2) (N : ℕ) :
    ¬ ∀ m ≥ N, (p m : ZMod 2) = c := by
  intro hc
  -- The pentagonal number `G = pent k₀`, where `k₀ = j + 1` and `j = N + 1`.
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j = N + 1 := ⟨_, rfl⟩
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℤ, k₀ = (j : ℤ) + 1 := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℕ, G = (pent k₀).toNat := ⟨_, rfl⟩
  have hGz : (G : ℤ) = pent k₀ := by rw [hG]; exact Int.toNat_of_nonneg (pent_nonneg k₀)
  have hpos : pent 0 < pent k₀ := by
    have h2 := two_mul_pent k₀
    have hk₀2 : (2 : ℤ) ≤ k₀ := by omega
    rw [pent_zero]
    nlinarith
  have hGbig : 2 * j + 1 ≤ G := by
    have := pent_gap j hk₀ 0 hpos
    rw [pent_zero] at this
    omega
  have hG1 : G - 1 ≠ 0 := by omega
  have hcastG1 : ((G - 1 : ℕ) : ℤ) = (G : ℤ) - 1 := by omega
  -- `{k : pent k ≤ G} = {k₀} ∪ {k : pent k ≤ G - 1}`.
  have hnot : k₀ ∉ Nat.Partition.kSet ((G - 1 : ℕ) : ℤ) := by
    rw [mem_kSet_iff, hcastG1]
    omega
  have hset : Nat.Partition.kSet (G : ℤ) =
      insert k₀ (Nat.Partition.kSet ((G - 1 : ℕ) : ℤ)) := by
    ext k
    rw [Finset.mem_insert, mem_kSet_iff, mem_kSet_iff, hcastG1]
    constructor
    · intro h
      rcases h.lt_or_eq with h | h
      · right; omega
      · left; exact pent_injective (h.trans hGz)
    · rintro (rfl | h)
      · omega
      · omega
  -- The recurrences at `G` and `G - 1`.
  have r1 := recurrence_mod_two G (by omega)
  have r2 := recurrence_mod_two (G - 1) hG1
  rw [hset, Finset.sum_insert hnot] at r1
  have hterm : (p (G - (pent k₀).toNat) : ZMod 2) = 1 := by
    rw [← hG, Nat.sub_self]
    simp [p]
  -- All other terms agree mod 2, since both arguments are `≥ N`.
  have hsum : ∑ k ∈ Nat.Partition.kSet ((G - 1 : ℕ) : ℤ), (p (G - (pent k).toNat) : ZMod 2)
      = ∑ k ∈ Nat.Partition.kSet ((G - 1 : ℕ) : ℤ),
          (p (G - 1 - (pent k).toNat) : ZMod 2) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [mem_kSet_iff, hcastG1] at hk
    have hlt : pent k < pent k₀ := by omega
    have hgap := pent_gap j hk₀ k hlt
    have hk0 : ((pent k).toNat : ℤ) = pent k := Int.toNat_of_nonneg (pent_nonneg k)
    rw [hc (G - (pent k).toNat) (by omega), hc (G - 1 - (pent k).toNat) (by omega)]
  rw [hterm, hsum, r2, add_zero] at r1
  exact absurd r1 (by decide)

/-- **Kolberg (1959).** `p n` is even for infinitely many `n`. -/
theorem infinite_even : {n : ℕ | Even (Fintype.card (Nat.Partition n))}.Infinite := by
  intro hfin
  obtain ⟨M, hM⟩ := hfin.bddAbove
  apply not_eventually_const 1 (M + 1)
  intro m hm
  rw [ZMod.natCast_eq_one_iff_odd, ← Nat.not_even_iff_odd]
  intro he
  have : m ≤ M := hM he
  omega

/-- **Kolberg (1959).** `p n` is odd for infinitely many `n`. -/
theorem infinite_odd : {n : ℕ | Odd (Fintype.card (Nat.Partition n))}.Infinite := by
  intro hfin
  obtain ⟨M, hM⟩ := hfin.bddAbove
  apply not_eventually_const 0 (M + 1)
  intro m hm
  rw [ZMod.natCast_eq_zero_iff_even, ← Nat.not_odd_iff_even]
  intro ho
  have : m ≤ M := hM ho
  omega

end Kolberg
