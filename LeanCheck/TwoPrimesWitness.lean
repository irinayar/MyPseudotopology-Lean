import Mathlib.Tactic

/-!
# Unit-target witnesses for the primes 2 and 3

For every integer `D` with `8 ≤ D ≤ 3000` there is an integer `k` from an explicit table with
`P₃(k) < 1/D` and `P₂(k - 1) < 1/D`, where `P_p(x) = sup_{n ≥ 1} ‖x / p^(n²)‖`.

This certifies that the least witness height `h_D(1)` is at most the tabulated value.
It does **not** certify minimality: no statement here excludes a smaller witness.
-/

namespace TwoPrimesWitness

/-- `‖x / p^(n²)‖ < 1/D` for every `n ≥ 1`, written without real numbers:
some multiple `j * p^(n²)` is closer to `x` than `p^(n²) / D`. -/
def Small (p D : ℕ) (x : ℤ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ j : ℤ, (D : ℤ) * |x - j * (p : ℤ) ^ (n ^ 2)| < (p : ℤ) ^ (n ^ 2)

/-- Test of one level for the absolute value `a`. -/
def level (p D a n : ℕ) : Bool :=
  decide (D * min (a % p ^ (n ^ 2)) (p ^ (n ^ 2) - a % p ^ (n ^ 2)) < p ^ (n ^ 2))

/-- Finite test: the levels `1, …, N` and a bound which settles all higher levels. -/
def check (p D a N : ℕ) : Bool :=
  (List.range N).all (fun i => level p D a (i + 1)) && decide (D * a < p ^ ((N + 1) ^ 2))

theorem small_of_check {p D a N : ℕ} {x : ℤ} (hp : 1 ≤ p) (ha : x.natAbs = a)
    (h : check p D a N = true) : Small p D x := by
  intro n hn
  unfold check at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hlev, htail⟩ := h
  have htail' : D * a < p ^ ((N + 1) ^ 2) := of_decide_eq_true htail
  have hx : x = (a : ℤ) ∨ x = -(a : ℤ) := by
    rcases Int.natAbs_eq x with h1 | h1
    · left; rw [ha] at h1; exact h1
    · right; rw [ha] at h1; exact h1
  rcases le_or_gt n N with hnN | hnN
  · have hmem : n - 1 ∈ List.range N := List.mem_range.mpr (by omega)
    have h1 := List.all_eq_true.mp hlev (n - 1) hmem
    have hn1 : n - 1 + 1 = n := by omega
    rw [hn1] at h1
    unfold level at h1
    have h2 := of_decide_eq_true h1
    obtain ⟨q, hq⟩ : ∃ q, q = p ^ (n ^ 2) := ⟨_, rfl⟩
    rw [← hq] at h2
    have hqpos : 0 < q := by rw [hq]; exact pow_pos (by omega) _
    have hpq : (p : ℤ) ^ (n ^ 2) = (q : ℤ) := by rw [hq]; push_cast; rfl
    have key : ∃ j : ℤ, |(a : ℤ) - j * q| = ((min (a % q) (q - a % q) : ℕ) : ℤ) := by
      have hr : a % q < q := Nat.mod_lt _ hqpos
      have hdm : (q : ℤ) * ((a / q : ℕ) : ℤ) + ((a % q : ℕ) : ℤ) = (a : ℤ) := by
        exact_mod_cast Nat.div_add_mod a q
      rcases le_total (a % q) (q - a % q) with hc | hc
      · refine ⟨((a / q : ℕ) : ℤ), ?_⟩
        rw [min_eq_left hc]
        have e : (a : ℤ) - ((a / q : ℕ) : ℤ) * q = ((a % q : ℕ) : ℤ) := by linear_combination -hdm
        rw [e, abs_of_nonneg (Int.natCast_nonneg _)]
      · refine ⟨((a / q : ℕ) : ℤ) + 1, ?_⟩
        rw [min_eq_right hc]
        have e : (a : ℤ) - (((a / q : ℕ) : ℤ) + 1) * q = -(((q - a % q : ℕ)) : ℤ) := by
          rw [Nat.cast_sub hr.le]; linear_combination -hdm
        rw [e, abs_neg, abs_of_nonneg (Int.natCast_nonneg _)]
    obtain ⟨j, hj⟩ := key
    have hlt : (D : ℤ) * ((min (a % q) (q - a % q) : ℕ) : ℤ) < (q : ℤ) := by exact_mod_cast h2
    rw [hpq]
    rcases hx with hx | hx
    · exact ⟨j, by rw [hx, hj]; exact hlt⟩
    · refine ⟨-j, ?_⟩
      have e : x - -j * (q : ℤ) = -((a : ℤ) - j * q) := by rw [hx]; ring
      rw [e, abs_neg, hj]; exact hlt
  · refine ⟨0, ?_⟩
    have hmono : p ^ ((N + 1) ^ 2) ≤ p ^ (n ^ 2) :=
      Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_left (by omega) 2)
    have h3 : D * a < p ^ (n ^ 2) := lt_of_lt_of_le htail' hmono
    have hax : |x| = (a : ℤ) := by rw [Int.abs_eq_natAbs, ha]
    rw [zero_mul, sub_zero, hax]
    exact_mod_cast h3

theorem small_mono {p D D' : ℕ} {x : ℤ} (hD : D' ≤ D) (h : Small p D x) : Small p D' x := by
  intro n hn
  obtain ⟨j, hj⟩ := h n hn
  refine ⟨j, lt_of_le_of_lt ?_ hj⟩
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hD) (abs_nonneg _)

/-- Rows `(first D, last D, k is negative, |k|)` of the table. -/
def rows : List (ℕ × ℕ × Bool × ℕ) := [
  (8, 8, true, 495),
  (9, 10, false, 561),
  (11, 11, false, 59937),
  (12, 12, false, 136161),
  (13, 15, true, 195615),
  (16, 26, true, 589839),
  (27, 30, false, 300874257),
  (31, 31, true, 301465071),
  (32, 48, false, 302054913),
  (49, 63, false, 7627190764545),
  (64, 66, false, 567690557129217),
  (67, 80, false, 149176171345412097),
  (81, 108, true, 18460259064110711295),
  (109, 122, true, 202779079158043311615),
  (123, 127, false, 221239333138120704513),
  (128, 131, true, 1826202334260327546879),
  (132, 135, false, 21775827999770731679252481),
  (136, 136, true, 21776196783782581432680447),
  (137, 158, true, 24167725152845635600187391),
  (159, 215, false, 24168444555598036601864193),
  (216, 227, false, 790645879243038298359136257),
  (228, 273, false, 1699742784904311585885913089),
  (274, 288, true, 271272912587040771759007688753151),
  (289, 291, false, 436067451928631059097302513811457),
  (292, 297, true, 436073735929155042118271995150335),
  (298, 342, true, 1497091661975858234431541486878719),
  (343, 426, false, 6235574354287680746877466424901633),
  (427, 437, false, 1773193774390740635777698089980259270657),
  (438, 492, false, 2661117905712444521795315205443696918529),
  (493, 503, false, 6207496413615241618428036085462998253569),
  (504, 511, true, 10641797555739376350943955148787857424383),
  (512, 524, false, 22258236488463918250117037830338644981841921),
  (525, 537, false, 22277302932527063577760992963673029424971777),
  (538, 626, false, 22288388693156243278093181614183599149416449),
  (627, 664, false, 66907291982889809579769849953882135494393857),
  (665, 682, false, 178421516210482934465929494559209061458378753),
  (683, 714, false, 223038646310390834811416967750970593196900353),
  (715, 904, true, 267606999048097958924495329266879805341564927),
  (905, 1120, true, 3741125670015037475948709243533782522015121768710143),
  (1121, 1236, false, 49387081570713244832701347396291781005378301963796481),
  (1237, 1256, false, 273873676242441116701313592707721579205917216308461569),
  (1257, 1342, false, 1232432057814408454036784532214053795128321173260075009),
  (1343, 1615, false, 1776437768433880923127647935037785295341903109681053697),
  (1616, 1626, false, 5423376028299848004567966146111441684691656434283657748807681),
  (1627, 1724, true, 8135065620216463951132126673962645980838747360804398960738303),
  (1725, 1789, true, 20890246212534628330869182115468662419725518867845637440798719),
  (1790, 1824, false, 76229178531383945285635887083627614786292187567511197037101057),
  (1825, 1880, false, 105254487979338943656842994332864468893748469832459722967482369),
  (1881, 1927, true, 495338701606222168155546332795509966811317868627031106193981439),
  (1928, 2047, true, 556101011996200011482287039280391378568921701166966875904540671),
  (2048, 2186, true, 2116437865908845520763853060430592621732868569044340911521136639),
  (2187, 2539, true, 3600545543154094609677280766474328023326431775463962453045411839),
  (2540, 2643, true, 31974478743809824023083700923595149503103120227863455640601517898072063),
  (2644, 2674, true, 305024842980725407768675616193970636262702752233073273007881735181959167),
  (2675, 2730, true, 578075192243890937744856812391565589766358854962168187476228328210300927),
  (2731, 3000, false, 746574855379523934620495553901496231006239480564725686872264764311994369)
]

/-- The witness of a row. -/
def witness (r : ℕ × ℕ × Bool × ℕ) : ℤ := if r.2.2.1 then -(r.2.2.2 : ℤ) else (r.2.2.2 : ℤ)

/-- Both tests of a row at the largest `D` of its block (20 explicit levels). -/
def rowOK (r : ℕ × ℕ × Bool × ℕ) : Bool :=
  check 3 r.2.1 (witness r).natAbs 20 && check 2 r.2.1 (witness r - 1).natAbs 20

theorem rows_ok : rows.all rowOK = true := by decide +kernel

theorem rows_cover :
    (List.range 2993).all (fun i => rows.any (fun r => decide (r.1 ≤ i + 8) && decide (i + 8 ≤ r.2.1)))
      = true := by decide +kernel

/-- Each row serves every `D` up to the end of its block. -/
theorem row_witness (r : ℕ × ℕ × Bool × ℕ) (hr : r ∈ rows) (D : ℕ) (hD : D ≤ r.2.1) :
    Small 3 D (witness r) ∧ Small 2 D (witness r - 1) := by
  have h := List.all_eq_true.mp rows_ok r hr
  unfold rowOK at h
  rw [Bool.and_eq_true] at h
  exact ⟨small_mono hD (small_of_check (by norm_num) rfl h.1),
    small_mono hD (small_of_check (by norm_num) rfl h.2)⟩

/-- For every `D` from `8` to `3000` the table contains a witness of the unit target. -/
theorem unit_witness (D : ℕ) (h8 : 8 ≤ D) (h3000 : D ≤ 3000) :
    ∃ r ∈ rows, r.1 ≤ D ∧ D ≤ r.2.1 ∧ Small 3 D (witness r) ∧ Small 2 D (witness r - 1) := by
  have hmem : D - 8 ∈ List.range 2993 := List.mem_range.mpr (by omega)
  have h := List.all_eq_true.mp rows_cover (D - 8) hmem
  have hD : D - 8 + 8 = D := by omega
  rw [hD] at h
  obtain ⟨r, hr, hb⟩ := List.any_eq_true.mp h
  rw [Bool.and_eq_true] at hb
  have h1 : r.1 ≤ D := of_decide_eq_true hb.1
  have h2 : D ≤ r.2.1 := of_decide_eq_true hb.2
  exact ⟨r, hr, h1, h2, row_witness r hr D h2⟩

end TwoPrimesWitness
