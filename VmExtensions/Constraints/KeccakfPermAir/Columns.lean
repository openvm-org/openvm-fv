import VmExtensions.Airs.KeccakfPermAir
import VmExtensions.Extraction.KeccakfPermAir

set_option linter.all false
set_option maxHeartbeats 1_000_000_000

namespace KeccakfPermAir.extraction

section helper_defs
  variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

  /-- 16-bit binary recomposition: `sum 2^i * bit[base+i] = output`.
  The AIR-generated argument tuples dispatch to the regenerated extraction constraints;
  the fallback keeps the semantic polynomial for generic uses. -/
  def recompose16_eq (c : C F ExtF) (bit_base output_col : ℕ) (row : ℕ) : Prop :=
    if bit_base = 2565 ∧ output_col = 2465 then constraint_3074 c row else
    if bit_base = 2581 ∧ output_col = 2466 then constraint_3075 c row else
    if bit_base = 2597 ∧ output_col = 2467 then constraint_3076 c row else
    if bit_base = 2613 ∧ output_col = 2468 then constraint_3077 c row else
    if bit_base = 2597 ∧ output_col = 2631 then constraint_3080 c row else
    let b (i : ℕ) := Circuit.main c (id := 0) (column := bit_base + i) (row := row) (rotation := 0)
    let out := Circuit.main c (id := 0) (column := output_col) (row := row) (rotation := 0)
    (b 0 + 2 * b 1 + 4 * b 2 + 8 * b 3 + 16 * b 4 + 32 * b 5 + 64 * b 6 + 128 * b 7 +
      256 * b 8 + 512 * b 9 + 1024 * b 10 + 2048 * b 11 + 4096 * b 12 + 8192 * b 13 +
      16384 * b 14 + 32768 * b 15 - out) = 0

  /-- 3-way XOR plus 16-bit recomposition.  AIR-generated tuples dispatch to
  the regenerated extraction constraints; the fallback keeps the semantic polynomial. -/
  def xor3_recompose16_eq (c : C F ExtF) : ℕ → ℕ → ℕ → ℕ → ℕ → Prop
    | 225, 545, 865, 125, row => constraint_954 c row
    | 241, 561, 881, 126, row => constraint_955 c row
    | 257, 577, 897, 127, row => constraint_956 c row
    | 273, 593, 913, 128, row => constraint_957 c row
    | 289, 609, 929, 129, row => constraint_1022 c row
    | 305, 625, 945, 130, row => constraint_1023 c row
    | 321, 641, 961, 131, row => constraint_1024 c row
    | 337, 657, 977, 132, row => constraint_1025 c row
    | 353, 673, 993, 133, row => constraint_1090 c row
    | 369, 689, 1009, 134, row => constraint_1091 c row
    | 385, 705, 1025, 135, row => constraint_1092 c row
    | 401, 721, 1041, 136, row => constraint_1093 c row
    | 417, 737, 1057, 137, row => constraint_1158 c row
    | 433, 753, 1073, 138, row => constraint_1159 c row
    | 449, 769, 1089, 139, row => constraint_1160 c row
    | 465, 785, 1105, 140, row => constraint_1161 c row
    | 481, 801, 1121, 141, row => constraint_1226 c row
    | 497, 817, 1137, 142, row => constraint_1227 c row
    | 513, 833, 1153, 143, row => constraint_1228 c row
    | 529, 849, 1169, 144, row => constraint_1229 c row
    | 225, 545, 1185, 145, row => constraint_1294 c row
    | 241, 561, 1201, 146, row => constraint_1295 c row
    | 257, 577, 1217, 147, row => constraint_1296 c row
    | 273, 593, 1233, 148, row => constraint_1297 c row
    | 289, 609, 1249, 149, row => constraint_1362 c row
    | 305, 625, 1265, 150, row => constraint_1363 c row
    | 321, 641, 1281, 151, row => constraint_1364 c row
    | 337, 657, 1297, 152, row => constraint_1365 c row
    | 353, 673, 1313, 153, row => constraint_1430 c row
    | 369, 689, 1329, 154, row => constraint_1431 c row
    | 385, 705, 1345, 155, row => constraint_1432 c row
    | 401, 721, 1361, 156, row => constraint_1433 c row
    | 417, 737, 1377, 157, row => constraint_1498 c row
    | 433, 753, 1393, 158, row => constraint_1499 c row
    | 449, 769, 1409, 159, row => constraint_1500 c row
    | 465, 785, 1425, 160, row => constraint_1501 c row
    | 481, 801, 1441, 161, row => constraint_1566 c row
    | 497, 817, 1457, 162, row => constraint_1567 c row
    | 513, 833, 1473, 163, row => constraint_1568 c row
    | 529, 849, 1489, 164, row => constraint_1569 c row
    | 225, 545, 1505, 165, row => constraint_1634 c row
    | 241, 561, 1521, 166, row => constraint_1635 c row
    | 257, 577, 1537, 167, row => constraint_1636 c row
    | 273, 593, 1553, 168, row => constraint_1637 c row
    | 289, 609, 1569, 169, row => constraint_1702 c row
    | 305, 625, 1585, 170, row => constraint_1703 c row
    | 321, 641, 1601, 171, row => constraint_1704 c row
    | 337, 657, 1617, 172, row => constraint_1705 c row
    | 353, 673, 1633, 173, row => constraint_1770 c row
    | 369, 689, 1649, 174, row => constraint_1771 c row
    | 385, 705, 1665, 175, row => constraint_1772 c row
    | 401, 721, 1681, 176, row => constraint_1773 c row
    | 417, 737, 1697, 177, row => constraint_1838 c row
    | 433, 753, 1713, 178, row => constraint_1839 c row
    | 449, 769, 1729, 179, row => constraint_1840 c row
    | 465, 785, 1745, 180, row => constraint_1841 c row
    | 481, 801, 1761, 181, row => constraint_1906 c row
    | 497, 817, 1777, 182, row => constraint_1907 c row
    | 513, 833, 1793, 183, row => constraint_1908 c row
    | 529, 849, 1809, 184, row => constraint_1909 c row
    | 225, 545, 1825, 185, row => constraint_1974 c row
    | 241, 561, 1841, 186, row => constraint_1975 c row
    | 257, 577, 1857, 187, row => constraint_1976 c row
    | 273, 593, 1873, 188, row => constraint_1977 c row
    | 289, 609, 1889, 189, row => constraint_2042 c row
    | 305, 625, 1905, 190, row => constraint_2043 c row
    | 321, 641, 1921, 191, row => constraint_2044 c row
    | 337, 657, 1937, 192, row => constraint_2045 c row
    | 353, 673, 1953, 193, row => constraint_2110 c row
    | 369, 689, 1969, 194, row => constraint_2111 c row
    | 385, 705, 1985, 195, row => constraint_2112 c row
    | 401, 721, 2001, 196, row => constraint_2113 c row
    | 417, 737, 2017, 197, row => constraint_2178 c row
    | 433, 753, 2033, 198, row => constraint_2179 c row
    | 449, 769, 2049, 199, row => constraint_2180 c row
    | 465, 785, 2065, 200, row => constraint_2181 c row
    | 481, 801, 2081, 201, row => constraint_2246 c row
    | 497, 817, 2097, 202, row => constraint_2247 c row
    | 513, 833, 2113, 203, row => constraint_2248 c row
    | 529, 849, 2129, 204, row => constraint_2249 c row
    | 225, 545, 2145, 205, row => constraint_2314 c row
    | 241, 561, 2161, 206, row => constraint_2315 c row
    | 257, 577, 2177, 207, row => constraint_2316 c row
    | 273, 593, 2193, 208, row => constraint_2317 c row
    | 289, 609, 2209, 209, row => constraint_2382 c row
    | 305, 625, 2225, 210, row => constraint_2383 c row
    | 321, 641, 2241, 211, row => constraint_2384 c row
    | 337, 657, 2257, 212, row => constraint_2385 c row
    | 353, 673, 2273, 213, row => constraint_2450 c row
    | 369, 689, 2289, 214, row => constraint_2451 c row
    | 385, 705, 2305, 215, row => constraint_2452 c row
    | 401, 721, 2321, 216, row => constraint_2453 c row
    | 417, 737, 2337, 217, row => constraint_2518 c row
    | 433, 753, 2353, 218, row => constraint_2519 c row
    | 449, 769, 2369, 219, row => constraint_2520 c row
    | 465, 785, 2385, 220, row => constraint_2521 c row
    | 481, 801, 2401, 221, row => constraint_2586 c row
    | 497, 817, 2417, 222, row => constraint_2587 c row
    | 513, 833, 2433, 223, row => constraint_2588 c row
    | 529, 849, 2449, 224, row => constraint_2589 c row
    | a_base, b_base, c_base, output_col, row =>
      let a (i : ℕ) := Circuit.main c (id := 0) (column := a_base + i) (row := row) (rotation := 0)
      let b (i : ℕ) := Circuit.main c (id := 0) (column := b_base + i) (row := row) (rotation := 0)
      let d (i : ℕ) := Circuit.main c (id := 0) (column := c_base + i) (row := row) (rotation := 0)
      let out := Circuit.main c (id := 0) (column := output_col) (row := row) (rotation := 0)
      let x3 (i : ℕ) :=
        a i + b i + d i - 2 * a i * b i - 2 * a i * d i - 2 * b i * d i + 4 * a i * b i * d i
      (x3 0 + 2 * x3 1 + 4 * x3 2 + 8 * x3 3 + 16 * x3 4 + 32 * x3 5 + 64 * x3 6 + 128 * x3 7 +
        256 * x3 8 + 512 * x3 9 + 1024 * x3 10 + 2048 * x3 11 + 4096 * x3 12 + 8192 * x3 13 +
        16384 * x3 14 + 32768 * x3 15 - out) = 0

  /-- Chi step plus 16-bit recomposition.  AIR-generated tuples dispatch to
  the regenerated extraction constraints; the fallback keeps the semantic polynomial. -/
  def chi_recompose16_eq (c : C F ExtF) : ℕ → ℕ → ℕ → ℕ → ℕ → Prop
    | 865, 1269, 1654, 2465, row => constraint_2910 c row
    | 881, 1285, 1670, 2466, row => constraint_2911 c row
    | 913, 1253, 1638, 2468, row => constraint_2913 c row
    | 1269, 1654, 2060, 2469, row => constraint_2914 c row
    | 1253, 1638, 2044, 2472, row => constraint_2917 c row
    | 1638, 2044, 2435, 2476, row => constraint_2921 c row
    | 2028, 2419, 897, 2479, row => constraint_2924 c row
    | 2044, 2435, 913, 2480, row => constraint_2925 c row
    | 2403, 881, 1285, 2482, row => constraint_2927 c row
    | 2435, 913, 1253, 2484, row => constraint_2929 c row
    | 1061, 1453, 1534, 2487, row => constraint_2932 c row
    | 1077, 1469, 1550, 2488, row => constraint_2933 c row
    | 1469, 1550, 1892, 2492, row => constraint_2937 c row
    | 1518, 1924, 2292, 2494, row => constraint_2939 c row
    | 1908, 2276, 1093, 2497, row => constraint_2942 c row
    | 2276, 1093, 1485, 2501, row => constraint_2946 c row
    | 2308, 1061, 1453, 2503, row => constraint_2948 c row
    | 960, 1339, 1704, 2507, row => constraint_2952 c row
    | 976, 1355, 1720, 2508, row => constraint_2953 c row
    | 1339, 1704, 2105, 2511, row => constraint_2956 c row
    | 1355, 1720, 2121, 2512, row => constraint_2957 c row
    | 1704, 2105, 2159, 2515, row => constraint_2960 c row
    | 1720, 2121, 2175, 2516, row => constraint_2961 c row
    | 2105, 2159, 960, 2519, row => constraint_2964 c row
    | 2121, 2175, 976, 2520, row => constraint_2965 c row
    | 2159, 960, 1339, 2523, row => constraint_2968 c row
    | 2175, 976, 1355, 2524, row => constraint_2969 c row
    | 1142, 1197, 1607, 2528, row => constraint_2973 c row
    | 1229, 1575, 1954, 2530, row => constraint_2975 c row
    | 1197, 1607, 1986, 2532, row => constraint_2977 c row
    | 1575, 1954, 2361, 2534, row => constraint_2979 c row
    | 1591, 1970, 2377, 2535, row => constraint_2980 c row
    | 1970, 2377, 1126, 2539, row => constraint_2984 c row
    | 2345, 1158, 1213, 2541, row => constraint_2986 c row
    | 995, 1386, 1786, 2545, row => constraint_2990 c row
    | 1011, 1402, 1802, 2546, row => constraint_2991 c row
    | 1386, 1786, 1848, 2549, row => constraint_2994 c row
    | 1402, 1802, 1864, 2550, row => constraint_2995 c row
    | 1802, 1864, 2223, 2554, row => constraint_2999 c row
    | 1770, 1832, 2255, 2556, row => constraint_3001 c row
    | 1864, 2223, 1011, 2558, row => constraint_3003 c row
    | 2223, 1011, 1402, 2562, row => constraint_3007 c row
    | 2239, 1027, 1418, 2563, row => constraint_3008 c row
    | a_base, b_base, c_base, output_col, row =>
      let a (i : ℕ) := Circuit.main c (id := 0) (column := a_base + i) (row := row) (rotation := 0)
      let b (i : ℕ) := Circuit.main c (id := 0) (column := b_base + i) (row := row) (rotation := 0)
      let d (i : ℕ) := Circuit.main c (id := 0) (column := c_base + i) (row := row) (rotation := 0)
      let out := Circuit.main c (id := 0) (column := output_col) (row := row) (rotation := 0)
      let ch (i : ℕ) := a i + d i - b i * d i - 2 * a i * d i + 2 * a i * b i * d i
      (ch 0 + 2 * ch 1 + 4 * ch 2 + 8 * ch 3 + 16 * ch 4 + 32 * ch 5 + 64 * ch 6 + 128 * ch 7 +
        256 * ch 8 + 512 * ch 9 + 1024 * ch 10 + 2048 * ch 11 + 4096 * ch 12 + 8192 * ch 13 +
        16384 * ch 14 + 32768 * ch 15 - out) = 0

end helper_defs

end KeccakfPermAir.extraction

namespace KeccakfPermAir.constraints

/-! ## Column Abbreviations

Named accessors for the 2634 main-trace columns of KeccakfPermAir.
Each abbreviation is definitionally equal to the corresponding `Circuit.main` call.

### Column layout

| Range       | Count | Name            | Description                          |
|-------------|-------|-----------------|--------------------------------------|
| 0–23        | 24    | step_flag       | One-hot round index (24 keccak-f rounds) |
| 24          | 1     | export_flag     | Row exports a permutation result     |
| 25–124      | 100   | preimage        | Input state (50 words × 2 u16 limbs) |
| 125–224     | 100   | a               | State after round                    |
| 225–544     | 320   | c_bit           | θ column-parity bits (5 × 64)        |
| 545–864     | 320   | c_prime_bit     | θ parity-prime bits (5 × 64)         |
| 865–2464    | 1600  | a_prime_bit     | θ result bits (5 × 5 × 64)           |
| 2465–2564   | 100   | a_prime_prime   | State after ρπ+χ                     |
| 2565–2628   | 64    | a_pp_00_bit     | Bits of a_prime_prime[0][0]           |
| 2629–2632   | 4     | a_ppp_00_limb   | ι result limbs for lane [0][0]       |
| 2633        | 1     | timestamp       | Bus timestamp                        |

Columns 0–224 also appear with rotation = 1 in transition constraints.
-/

section constraint_simplification
  variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

  /-! ### Scalar columns -/

  /-- Step flag for round `i` (cols 0–23, rotation 0). -/
  abbrev step_flag (c : C F ExtF) (i : ℕ) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := i) (row := row) (rotation := 0)

  /-- Step flag for round `i`, next row (cols 0–23, rotation 1). -/
  abbrev step_flag_next (c : C F ExtF) (i : ℕ) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := i) (row := row) (rotation := 1)

  /-- Export flag (col 24). -/
  abbrev export_flag (c : C F ExtF) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)

  /-! ### Preimage columns (cols 25–124) -/

  /-- Preimage value at flat index `i` (cols 25–124, i ∈ [0, 100)). -/
  abbrev preimage (c : C F ExtF) (i : ℕ) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 25 + i) (row := row) (rotation := 0)

  /-- Preimage value at flat index `i`, next row (rotation 1). -/
  abbrev preimage_next (c : C F ExtF) (i : ℕ) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 25 + i) (row := row) (rotation := 1)

  /-! ### State columns (cols 125–224) -/

  /-- State value at flat index `i` (cols 125–224, i ∈ [0, 100)). -/
  abbrev a (c : C F ExtF) (i : ℕ) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 125 + i) (row := row) (rotation := 0)

  /-- State value at flat index `i`, next row (rotation 1). -/
  abbrev a_next (c : C F ExtF) (i : ℕ) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 125 + i) (row := row) (rotation := 1)

  /-! ### θ parity bits (cols 225–544) -/

  /-- θ column-parity bit at flat index `i` (cols 225–544, i ∈ [0, 320)). -/
  abbrev c_bit (c : C F ExtF) (i : ℕ) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 225 + i) (row := row) (rotation := 0)

  /-! ### θ parity-prime bits (cols 545–864) -/

  /-- θ parity-prime bit at flat index `i` (cols 545–864, i ∈ [0, 320)). -/
  abbrev c_prime_bit (c : C F ExtF) (i : ℕ) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 545 + i) (row := row) (rotation := 0)

  /-! ### θ result bits (cols 865–2464) -/

  /-- θ result bit at flat index `i` (cols 865–2464, i ∈ [0, 1600)). -/
  abbrev a_prime_bit (c : C F ExtF) (i : ℕ) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 865 + i) (row := row) (rotation := 0)

  /-! ### State after ρπ+χ (cols 2465–2564) -/

  /-- State after ρπ+χ at flat index `i` (cols 2465–2564, i ∈ [0, 100)). -/
  abbrev a_prime_prime (c : C F ExtF) (i : ℕ) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 2465 + i) (row := row) (rotation := 0)

  /-! ### ι support columns -/

  /-- Bits of a_prime_prime[0][0] at index `i` (cols 2565–2628, i ∈ [0, 64)). -/
  abbrev a_pp_00_bit (c : C F ExtF) (i : ℕ) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 2565 + i) (row := row) (rotation := 0)

  /-- ι result limb `i` for lane [0][0] (cols 2629–2632, i ∈ [0, 4)). -/
  abbrev a_ppp_00_limb (c : C F ExtF) (i : ℕ) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 2629 + i) (row := row) (rotation := 0)

  /-- Timestamp column (col 2633). -/
  abbrev timestamp (c : C F ExtF) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 2633) (row := row) (rotation := 0)

end constraint_simplification

end KeccakfPermAir.constraints
