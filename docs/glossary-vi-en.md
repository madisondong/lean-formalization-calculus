# Thuật ngữ và quy ước Việt–Lean

Với tên khai báo của dự án, dùng không gian tên của mô-đun tương ứng.
Các lỗi và bản sửa của giáo trình được ghi trong [đính chính](errata.md).

## Logic

| Thuật ngữ | Tiếng Anh | Lean | Ý nghĩa và quy ước |
| --- | --- | --- | --- |
| Mệnh đề | proposition | `Prop` | Phát biểu có giá trị đúng hoặc sai. |
| Phủ định | negation | `Not`, `¬ P` | `¬ P` nghĩa là `P → False`; luật phủ định kép dùng logic cổ điển. |
| Hội / tuyển | conjunction / disjunction | `∧`, `∨` | `P ∧ Q` đúng khi cả hai vế đúng; `P ∨ Q` đúng khi ít nhất một vế đúng. |
| Kéo theo | implication | `P → Q` | Nếu `P` đúng thì `Q` đúng. |
| Khi và chỉ khi | if and only if | `P ↔ Q` | `P → Q` và `Q → P`. |
| Hằng đúng / hằng sai | tautology / contradiction | `Tautology`, `Contradiction` | Mẫu công thức đúng hoặc sai với mọi phép gán. |
| Tương đương logic | logical equivalence | `LogicallyEquivalent` | Hai mẫu công thức có cùng giá trị chân lý với mọi phép gán. |
| Hệ quả logic | logical consequence | `LogicalConsequence` | Với mọi phép gán, nếu mọi tiền đề đúng thì kết luận đúng. |
| Với mọi / tồn tại / tồn tại duy nhất | for all / exists / exists uniquely | `∀`, `∃`, `∃!` | Thứ tự lượng từ quyết định các biến mà nhân chứng tồn tại có thể phụ thuộc vào. |

## Tập hợp và ánh xạ

| Thuật ngữ | Tiếng Anh | Lean | Ý nghĩa và quy ước |
| --- | --- | --- | --- |
| Tập hợp / tập hữu hạn | set / finite set | `Set α`, `Finset α` | `Set α` biểu diễn tập con của `α`; `Finset α` biểu diễn tập hữu hạn. |
| Tập con | subset | `A ⊆ B` | Trong sách, `⊂` thường có nghĩa là `⊆`; bao hàm ngặt cần thêm `A ≠ B`. |
| Phần bù trong `X` | relative complement | `X \ A` | Các phần tử thuộc `X` nhưng không thuộc `A`. |
| Hiệu đối xứng | symmetric difference | `A ∆ B` | Gồm các phần tử thuộc đúng một trong hai tập. |
| Ảnh / ảnh ngược | image / preimage | `f '' A`, `f ⁻¹' B` | Ảnh gồm các giá trị `f x` với `x ∈ A`; ảnh ngược gồm các `x` có `f x ∈ B`. |
| Đơn ánh / toàn ánh / song ánh | injective / surjective / bijective | `Function.Injective`, `Function.Surjective`, `Function.Bijective`; `Set.InjOn`, `Set.SurjOn`, `Set.BijOn` | Các phiên bản có hậu tố `On` xét các tập đã cho; các phiên bản còn lại xét toàn kiểu. |
| Đếm được / vô hạn đếm được | countable / countably infinite | `Countable`, `CountablyInfinite` | Đếm được cho phép tập hữu hạn; vô hạn đếm được nghĩa là có song ánh với `ℕ+`. |
| Quan hệ tương đương / lớp tương đương | equivalence relation / equivalence class | `Equivalence R`, `equivalenceClass R x` | Lớp của `x` gồm các `y` thỏa `R y x`; tính đối xứng cho phép viết `R x y`. |
| Quan hệ thứ tự bộ phận | partial order relation | `IsPartialOrderRelation` | Quan hệ phản xạ, phản đối xứng và bắc cầu; không yêu cầu mọi cặp phần tử so sánh được. |
| Phân hoạch | partition | `IsNonemptyPartition` | Các phần không rỗng, đôi một rời nhau và phủ toàn bộ tập nền không rỗng. |
| Khoảng / đoạn | open / closed interval | `Ioo`, `Icc`, `Ioc`, `Ico` | Sách yêu cầu `a < b` cho khoảng, đoạn hữu hạn. Trong mathlib, `Icc a a = {a}`. |
| Giá trị tuyệt đối | absolute value | `abs` | Trên `ℝ`, chuẩn trùng với giá trị tuyệt đối. |
| Cận trên bé nhất / phần tử lớn nhất | supremum / maximum | `IsLUB`, `IsGreatest` | Phần tử lớn nhất phải thuộc tập. Với tập thực không rỗng, bị chặn trên, `sSup` là cận trên bé nhất và có thể nằm ngoài tập. |
| Cận dưới lớn nhất / phần tử nhỏ nhất | infimum / minimum | `IsGLB`, `IsLeast` | Phần tử nhỏ nhất phải thuộc tập. Với tập thực không rỗng, bị chặn dưới, `sInf` là cận dưới lớn nhất và có thể nằm ngoài tập. |
| Số thực mở rộng | extended real numbers | `EReal`, `⊥`, `⊤` | `⊥ = −∞`, `⊤ = +∞`; trong `EReal`, `sSup ∅ = ⊥` và `sInf ∅ = ⊤`. |
| Khai triển thập phân tuần hoàn từ một vị trí | eventually periodic decimal expansion | `EventuallyPeriodicDigits` | Từ một vị trí trở đi, các chữ số lặp lại với một chu kì dương. |

## Dãy số

| Thuật ngữ | Tiếng Anh | Lean | Ý nghĩa và quy ước |
| --- | --- | --- | --- |
| Số tự nhiên của giáo trình | positive natural numbers | `ℕ+` | Sách dùng `ℕ = {1, 2, …}`, còn `Nat` có cả 0. Với dãy chỉ xét từ 1, giá trị tại 0 là phần mở rộng phụ. |
| Dãy số | sequence | `ℕ+ → ℝ`, `Nat → ℝ` | Ánh xạ từ tập chỉ số vào `ℝ`. |
| Hội tụ về `a` | convergence | `Chapter02.Section03.ConvergesTo u a` | Với mọi `ε > 0`, tồn tại `N ≥ 1` sao cho `\|u n − a\| < ε` với mọi `n ≥ N`; tương đương `Tendsto u atTop (𝓝 a)`. |
| Dãy con | subsequence | `IsSequenceSubsequence` | Có `φ` tăng ngặt trên `Ici 1`, với `φ k ≥ 1` và `v k = u (φ k)` cho mọi `k ≥ 1`. |
| Dãy Cauchy / dãy cơ bản | Cauchy sequence | `SequenceCauchy`, `CauchySeq` | Với mọi `ε > 0`, tồn tại `N ≥ 1` sao cho `\|u m − u n\| < ε` với mọi `m, n ≥ N`. |
| Tiến tới `+∞` / `−∞` | divergence to infinity | `SequenceTendsToPosInfinity`, `SequenceTendsToNegInfinity` | Với mỗi `M ∈ ℝ`, mọi số hạng từ một chỉ số đủ lớn đều lớn hơn `M`, hoặc đều nhỏ hơn `M`, tùy phía giới hạn. |
| Giới hạn trên / giới hạn dưới | limsup / liminf | `sequenceLimsup`, `sequenceLiminf` | Trong `EReal`, lần lượt là cận dưới lớn nhất của các cận trên bé nhất của đuôi và cận trên bé nhất của các cận dưới lớn nhất của đuôi. |
| Tăng / giảm | increasing / decreasing | `SequenceIncreasing`, `SequenceDecreasing` | Với mọi `n ≥ 1`, lần lượt có `u n ≤ u (n + 1)` hoặc `u (n + 1) ≤ u n`. |
| Đơn điệu | monotonic | `SequenceMonotonic` | Dãy tăng hoặc giảm. `MonotoneOn u (Ici 1)` chỉ biểu diễn chiều tăng; chiều giảm dùng `AntitoneOn`. |
| Tập giá trị và tính bị chặn của dãy | range and boundedness of a sequence | `sequenceRangeFromOne`, `SequenceBoundedAbove`, `SequenceBoundedBelow`, `SequenceBounded` | Các cận xét trên `u '' Ici 1`; dãy bị chặn khi có cả cận trên và cận dưới. |
| Tăng ngặt / giảm ngặt | strictly increasing / decreasing | `StrictMonoOn`, `StrictAntiOn` | Với hai chỉ số trong miền, `m < n` kéo theo `u m < u n` hoặc `u n < u m`. |
| Trung bình nhân (trung bình hình học) | geometric mean | `geometricMean`, `Real.rpow` | Với `n ≥ 1` và `x₁, …, xₙ > 0`, bằng `(x₁ ⋯ xₙ)^(1/n)`. |
| Trung bình điều hòa | harmonic mean | `harmonicMean x n` | Với `n ≥ 1` và `x₁, …, xₙ > 0`, bằng `n / (1/x₁ + ⋯ + 1/xₙ)`. |
| Dãy đoạn lồng nhau | nested intervals | `NestedClosedIntervals` | Mỗi `Icc aₙ bₙ` không rỗng và `Iₙ₊₁ ⊆ Iₙ` với `n ≥ 1`. |
| Sai phân liên tiếp co theo cấp số nhân | geometric contraction of successive differences | `SequenceHasContractiveDifferences` | Có `0 ≤ q < 1` sao cho `\|u (n + 2) − u (n + 1)\| ≤ q * \|u (n + 1) − u n\|` với mọi `n ≥ 1`. |
| Tập điểm tụ trong số thực mở rộng | cluster set in the extended real line | `extendedSequenceClusterSet` | Các giới hạn dãy con trong `EReal`, kể cả `−∞` và `+∞`. |
| Trung bình Cesàro | Cesàro mean | `cesaroMean` | Với `n ≥ 1`, bằng `(u 1 + ⋯ + u n) / n`. |
| Đủ lớn | eventually | `∀ᶠ n : ℕ in Filter.atTop, P n` | Có `N` sao cho `P n` đúng với mọi `n ≥ N`; `N` có thể phụ thuộc vào các tham số đã cho. |

## Giới hạn và tính liên tục

| Thuật ngữ | Tiếng Anh | Lean | Ý nghĩa và quy ước |
| --- | --- | --- | --- |
| Giới hạn tại điểm | punctured limit | `DomainLimit` | Xét khi `x ∈ D \ {a}` tiến tới `a`, với `a` là điểm tụ của `D`. Điều kiện ε–δ riêng chưa bao gồm giả thiết điểm tụ. |
| Giới hạn một phía | one-sided limit | `DomainLeftLimit`, `DomainRightLimit` | Xét các điểm của miền tiến đến `a` từ trái hoặc từ phải; `a` phải là điểm tụ từ phía tương ứng. |
| Vô cùng bé | infinitesimal | `InfinitesimalAlong` | Hàm tiến về 0 theo lọc tiếp cận khác `⊥`. |
| Vô cùng lớn về độ lớn | infinite magnitude | `InfiniteMagnitudeAlong` | Trị tuyệt đối tiến tới `+∞`; hàm có thể đổi dấu. |
| Vô cùng bé tương đương | equivalent infinitesimals | `EquivalentInfinitesimalsAlong` | Hai hàm tiến về 0 và thương tiến về 1; mẫu khác 0 khi đủ gần theo lọc tiếp cận. |
| Vô cùng bé cùng bậc | infinitesimals with a finite nonzero ratio limit | `InfinitesimalsWithNonzeroRatioLimitAlong` | Hai hàm tiến về 0; thương có giới hạn hữu hạn khác 0. Điều kiện này mạnh hơn so sánh `Θ`. |
| Bậc `α` của vô cùng bé so với `φ` | power order | `InfinitesimalPowerOrderAlong` | `α > 0`, hai hàm `f, φ` tiến về 0 và `f / φ^α` có giới hạn hữu hạn khác 0. Lũy thừa phải xác định khi đủ gần theo lọc tiếp cận. |
| Miền thực của lũy thừa | domain of real exponentiation | `realPowerDomain`, `EventuallyRealPowerDefinedAlong` | Theo quy ước của sách: số mũ nguyên dương cho phép mọi cơ số thực; số mũ nguyên không dương loại cơ số 0; số mũ không nguyên đòi cơ số dương. Điều kiện theo lọc yêu cầu cơ số thuộc miền này trên một tập thuộc lọc tiếp cận. |
| Căn bậc ba thực | real cube root | `signedCubeRoot` | Nghiệm thực duy nhất của `y³ = x` với mọi `x ∈ ℝ`. |
| Liên tục trên tập | continuity on a set | `DomainContinuousAt`, `DomainContinuousOn` | Tại `a`, yêu cầu `a ∈ D` và `f(x) → f(a)` khi `x ∈ D` tiến tới `a`. Liên tục trên `D` nghĩa là thỏa điều kiện này tại mọi điểm của `D`. |
| Liên tục đều | uniform continuity | `NonemptyUniformContinuousOn D f` | `D` không rỗng. Với mỗi `ε > 0`, có một `δ > 0` dùng chung cho mọi cặp điểm trong `D`. |
| Không liên tục đều | not uniformly continuous | `¬ UniformContinuousOn f D` | Có `ε > 0` sao cho với mọi `δ > 0`, tồn tại `u, v ∈ D` cách nhau dưới `δ` nhưng hai ảnh cách nhau ít nhất `ε`. |
| Liên tục Hölder | Hölder continuity | `NonemptyHolderContinuousOn` | `D` không rỗng; có `L ≥ 0`, `α > 0` sao cho `\|f u - f v\| ≤ L * \|u - v\|^α` với mọi `u, v ∈ D`. Không yêu cầu `α ≤ 1`. |
| Liên tục Lipschitz | Lipschitz continuity | `NonemptyLipschitzOn`, `LipschitzOnWith` | `D` không rỗng; có `L ≥ 0` sao cho `\|f u - f v\| ≤ L * \|u - v\|` với mọi `u, v ∈ D`. |
| Tiêu chuẩn dãy của liên tục đều | sequential criterion | `PositiveIndexUniformContinuitySequenceCriterionOn` | Với mọi hai dãy `u_n, v_n ∈ D` (`n ≥ 1`), nếu `u_n - v_n → 0` thì `f(u_n) - f(v_n) → 0`. |
| Mở rộng liên tục lên đoạn | continuous extension | `ContinuousOn F (Set.Icc a b)`, `Set.EqOn F f (Set.Ioo a b)` | Có hàm liên tục trên `[a, b]` và trùng với hàm đã cho trên `(a, b)`, với `a < b`. |
| Phép nhúng trù mật | dense inclusion | `DenseRange (Set.inclusion Ioo_subset_Icc_self)` | Khi `a < b`, bao đóng của `(a, b)` là `[a, b]`. |
| Hàm bị chặn | bounded function | `FunctionBoundedOn` | Có cận dưới và cận trên cho toàn bộ miền đang xét. |
| Phần âm có dấu | signed negative part | `signedNegativePart` | Giá trị tại `x` là `min (f x) 0`, nên không dương. |
| Đi ra ngoài mọi tập compact | escaping every compact set | `Filter.cocompact` | Trên kiểu con `[a, +∞)`, lọc này trùng với lọc tiến tới `+∞`. |
| Đạt cận dưới lớn nhất | attained infimum | `IsLeast` | Có `x₀ ∈ D` sao cho `f(x₀) ≤ f(x)` với mọi `x ∈ D`. |
| Chu kì dương trên miền | positive forward period on a domain | `HasPositiveForwardPeriodOn`, `HasPositiveForwardPeriod` | `T > 0`; mọi `x ∈ D` đều thỏa `x + T ∈ D` và `f(x + T) = f(x)`. Chỉ yêu cầu miền ổn định khi dịch tiến; chu kì không nhất thiết nhỏ nhất. |

Trong Lean, trên `ℝ`, ta có `x / 0 = 0`; các công thức của sách vẫn giữ điều kiện xác định.

## Đạo hàm và Taylor

| Thuật ngữ | Tiếng Anh | Lean | Ý nghĩa và quy ước |
| --- | --- | --- | --- |
| Khả vi / đạo hàm | differentiability / derivative | `DifferentiableAt`, `HasDerivAt`, `HasDerivativeWithinAt` | Khả vi tại `x` với đạo hàm `d`. Khi chỉ xét miền `I`, thương sai phân tiến về `d` trên `I \ {x}`. |
| Hạn chế của đạo hàm | restricted derivative / restricted iterated derivative within a set | `restrictedDerivative`, `restrictedIteratedDerivativeWithin` | Đạo hàm trên `ℝ` và đạo hàm lặp theo miền `I`, đều chỉ lấy giá trị tại các điểm của `I`. |
| Khả vi trên đoạn | differentiability on a closed interval | `DifferentiableOnClosedInterval` | Khả vi trong `(a, b)`, có đạo hàm phải hữu hạn tại `a` và đạo hàm trái hữu hạn tại `b`. |
| Khả vi đến cấp `n` trên đoạn | repeated differentiability | `DifferentiableToOrderOnClosedInterval` | Với `a < b`, có đạo hàm đến cấp `n` trong `(a, b)` và đạo hàm một phía đến cấp `n` tại hai đầu. Không yêu cầu đạo hàm cấp `n` liên tục. |
| Lớp `Cⁿ` và hàm trơn trên miền | Cⁿ regularity / smoothness on a domain | `DomainC`, `DomainSmooth` | Khả vi đến cấp `n` với đạo hàm cấp `n` liên tục; trơn là khả vi mọi cấp. Các đạo hàm tính theo miền `I`; định lí tương đương với `ContDiffOn` dùng `I` mở. |
| Đa thức Taylor đến cấp `n` | Taylor polynomial | `taylorPolynomialWithin` | Hệ số bậc `k` là `iteratedDerivWithin k f I x₀ / k!`, với `0 ≤ k ≤ n`; khai triển theo các lũy thừa của `x - x₀`. |
| Phần dư Peano | Peano remainder | `(fun x ↦ f x - P x) =o[𝓝[I] x₀] (fun x ↦ (x - x₀)^n)` | Với mỗi `ε > 0`, sai số tuyệt đối không vượt quá `ε * \|x - x₀\|^n` khi `x ∈ I` đủ gần tâm. |
| Miền khai triển tại 0 | interval of expansion | `Set.uIcc (0 : ℝ) x` | Miền phải chứa toàn đoạn nối 0 với `x`, kể cả hai đầu. |
| Dạng vô cùng trên vô cùng | infinity over infinity | `InfinityOverInfinityForm` | Tử và mẫu đều có giới hạn `+∞` hoặc `−∞`; cho phép hai dấu khác nhau. |
| Cận của hàm và đạo hàm trên `ℝ` | global bounds for a function and its derivatives | `BddAbove (Set.range fun x ↦ \|f x\|)`, `sSup` | Lấy cận trên cho giá trị tuyệt đối của hàm hoặc đạo hàm trên toàn `ℝ`. Khi tập giá trị bị chặn trên, dùng cận trên bé nhất của nó. |
| Tăng / giảm của hàm | monotonicity of a function | `FunctionIncreasing`, `FunctionDecreasing`, `FunctionMonotonic` | Tăng và giảm dùng bất đẳng thức không ngặt; đơn điệu nghĩa là tăng hoặc giảm. Tính ngặt dùng `<` hoặc `>`. |
| Cực trị địa phương trên miền | local extrema on a domain | `IsLocalMinimumOn`, `IsLocalMaximumOn`, `IsLocalExtremumOn` | `c ∈ D`; trên phần của `D` trong một lân cận của `c`, hàm đạt giá trị nhỏ nhất hoặc lớn nhất tại `c`. |
| Cực trị theo đạo hàm cấp cao | higher derivative tests for local extrema | `ContDiffOn ℝ n f`, `iteratedDeriv` | Giả sử `n > 0`, hàm thuộc `Cⁿ` gần `x₀`, `f(x₀) = 0` và các đạo hàm cấp `1 ≤ k < n` bằng 0 tại `x₀`. Nếu đạo hàm cấp `n` khác 0: `n` chẵn cho cực tiểu khi dương, cực đại khi âm; `n` lẻ không có cực trị. |
| Điểm uốn theo quy ước của sách | inflection point | `SourceInflectionOn` | Trong một khoảng chứa điểm đang xét, hàm khả vi tại các điểm khác và có đạo hàm hữu hạn hoặc vô cùng hai phía tại chính điểm ấy. Hàm lồi một phía, lõm phía kia; tính lồi/lõm không ngặt nên định nghĩa này cũng cho phép hàm afin. |

## Hình học và đơn vị

| Thuật ngữ | Tiếng Anh | Lean | Ý nghĩa và quy ước |
| --- | --- | --- | --- |
| Khảo sát hàm số | function investigation | Tên mô-đun chứa `FunctionInvestigation` | Xét miền xác định, giới hạn, biến thiên, cực trị, tính lồi lõm và các tiệm cận. |
| Khảo sát đường cong tham số | parametric curve investigation | Tên mô-đun chứa `ParametricCurveInvestigation` | Đường cong cho bằng các hàm tọa độ theo tham số; tham số không nhất thiết là hoành độ. |
| Khảo sát đường cong cực | polar curve investigation | Tên mô-đun chứa `PolarCurveInvestigation` | Đường cong cho bằng quan hệ giữa bán kính và góc. |
| Đạo hàm cấp hai / độ cong có dấu | second derivative / signed curvature | `deriv (deriv f)`; `conchoidSignedCurvatureNumerator` (tử số) | `f″` khác độ cong. Với `x′² + y′² > 0`, độ cong có dấu là `(x′y″ - y′x″)/(x′² + y′²)^(3/2)`. |
| Tọa độ cực với bán kính có dấu | signed polar coordinates | `signedPolarPoint r θ` trên `ℂ` | Cho phép `r < 0`; góc đo bằng radian và khoảng cách đến gốc bằng `\|r\|`. |
| Tọa độ cực duy nhất | uniqueness of positive-radius polar coordinates | `existsUnique_positive_polar_coordinates` | Mỗi điểm khác gốc có duy nhất một cặp tọa độ cực `(r, θ)` với `r > 0`, `0 ≤ θ < 2π`. Tại gốc, `r = 0` và góc tùy ý. |
| Công thức ngược tọa độ cực | inverse polar-coordinate formulas | `repaired_nonnegative_polar_inverse` | Với `(x, y) = (r cos θ, r sin θ)`, `r ≥ 0` và `x ≠ 0`, ta có `r = √(x² + y²)` và `tan θ = y/x`. |
| Tiệm cận trên miền `D` | asymptotes on a domain | `HasVerticalAsymptoteWithinAt`, `HasHorizontalAsymptoteWithin`, `HasObliqueAsymptoteWithin` | Xét giới hạn trên `D` tại điểm tụ từ phía tương ứng, hoặc ở phía vô cực nơi `D` không bị chặn. Tiệm cận xiên có hệ số góc khác 0. |
| Chi phí nghìn đồng / doanh thu đồng | cost in thousands of đồng / revenue in đồng | `companyCostThousands`, `companyRevenue`, `correctedProfit` | Nhân chi phí với 1000 trước khi trừ khỏi doanh thu. |
| Hàm cầu afin | affine demand function | `promotionPrice`, `promotion_affine_calibration_unique` | Trong mô hình `p(x) = mx + b`, hai giá trị tại hai sản lượng khác nhau xác định duy nhất `m, b`. |
| Dấu phẩy thập phân | decimal comma | — | Phân biệt dấu phẩy trong số với dấu tách biến hoặc đầu mút khoảng. |

Các công thức tọa độ cực dùng `ℂ` với chuẩn Euclid. Trên `ℝ × ℝ`, chuẩn mặc định là chuẩn cực đại.
