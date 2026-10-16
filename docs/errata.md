# Đính chính và các phát biểu được sửa

Mỗi mục ghi vị trí và trạng thái của phát biểu gốc, rồi nêu bản sửa hoặc phản ví dụ.
[Hai bài thay thế](#hai-bai-thay-the) được phát biểu riêng.

Các bài chưa có chứng minh Lean giữ phát biểu gốc
và dùng `by sorry` tại đúng mục. Mã sửa và phản ví dụ từ hai mô-đun tổng hợp cũ
được giữ trong chú thích ngay trước các bài này.

Tra theo chương: [Chương 1](#chuong-1) · [Chương 2](#chuong-2) ·
[Chương 3](#chuong-3) · [Chương 4](#chuong-4) · [Hai bài thay thế](#hai-bai-thay-the).

<a id="chuong-1"></a>

## Chương 1

<a id="c01-s04-exercise-007"></a>

### C01-S04-exercise-007

Nguồn: `source/Ch1_taphop.tex` L903-L905; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Số thực x là số đại số khi tồn tại một đa thức p **khác 0**, có hệ số nguyên và thỏa p(x)=0. Với định nghĩa này, chứng minh √2, ∛2 và ∛(1 + √5) là các số đại số.

<a id="c01-s04-exercise-016p02"></a>

### C01-S04-exercise-016.p02

Nguồn: `source/Ch1_taphop.tex` L1090-L1090; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Giả sử D đối xứng: với mọi x∈D, ta có −x∈D. Hàm `f : D → ℝ` chẵn khi và chỉ khi với mọi x∈D, `f(-x)=f(x)`. Phủ định của điều kiện này là: tồn tại x∈D sao cho `f(-x)≠f(x)`.

<a id="c01-s04-exercise-016p06"></a>

### C01-S04-exercise-016.p06

Nguồn: `source/Ch1_taphop.tex` L1094-L1094; trạng thái gốc: **FALSE AS STATED**.

**Bản sửa.** Hàm f Lipschitz trên D khi và chỉ khi tồn tại L≥0 sao cho `|f(x)-f(y)|≤L|x-y|` với mọi x,y∈D. Phủ định là: với mỗi L≥0, tồn tại x,y∈D sao cho `|f(x)-f(y)|>L|x-y|`.

Thêm thừa số `|x-y|` còn thiếu trong bản in.

<a id="c01-s04-example-009"></a>

### C01-S04-example-009

Nguồn: `source/Ch1_taphop.tex` L1365-L1395; trạng thái gốc: **FALSE AS STATED**.

**Bản sửa.** Trong công thức đầu tiên định nghĩa [0], thay `mod m` bằng `mod 5`. Giữ năm lớp `[r]={5k+r:k∈Z}`, với r=0,…,4, cùng tính tuần hoàn, tập thương, phân hoạch và hợp của chúng. Trong phát biểu tổng quát cuối ví dụ, dùng quy ước m là số nguyên và m>1.

<a id="c01-s05-remark-001"></a>

### C01-S05-remark-001

Nguồn: `source/Ch1_taphop.tex` L1630-L1633; trạng thái gốc: **FALSE AS STATED**.

**Bản sửa.** Thay cả hai dẫn chiếu đến phần (ii) của định lí bằng phần (iii). Các bao hàm liên quan đến ảnh của giao và ảnh của hiệu có thể là bao hàm thực sự; đẳng thức ảnh của hợp ở phần (ii) luôn đúng. Giữ mọi phép tính tập hợp đã in cho ánh xạ bình phương.

<a id="c01-s05-exercise-009"></a>

### C01-S05-exercise-009

Nguồn: `source/Ch1_taphop.tex` L1982-L1987; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Ánh xạ `f:X→Y` đơn ánh khi và chỉ khi, với mọi tập chỉ số I **không rỗng** và mọi họ các tập con A_i của X, ta có

`f(⋂_(i∈I) A_i)=⋂_(i∈I) f(A_i)`.

Bản sửa nêu lại quy ước họ không rỗng tại L677. Điều này không tự giải quyết cách viết “tập chỉ số bất kỳ” mâu thuẫn với quy ước ấy tại L1682.

<a id="chuong-2"></a>

## Chương 2

<a id="c02-s01-definition-006p01"></a>

### C02-S01-definition-006.p01

Nguồn: `source/Ch2_dayso.tex` L203-L204; trạng thái gốc: **BLOCKED**.

Trong lời dẫn ở L201, dùng thống nhất biến `β` thay cho `α`.
Tiểu mục này yêu cầu `β ≤ x` với mọi `x ∈ A`, tức `β` là cận dưới của `A`.
Giữ nguyên điều kiện đã in ở tiểu mục.

Kết hợp với tiểu mục kế tiếp, hai điều kiện đặc trưng cho `IsGLB A β`.
Định nghĩa này không khẳng định mọi tập đều có cận dưới lớn nhất.
Chứng minh: `calculus.Chapter02.Section01.greatestLowerBound_definition`.

<a id="c02-s01-definition-006p02"></a>

### C02-S01-definition-006.p02

Nguồn: `source/Ch2_dayso.tex` L205-L206; trạng thái gốc: **BLOCKED**.

Dùng cùng biến `β` trong lời dẫn ở L201. Tiểu mục này yêu cầu mọi cận dưới `m`
của `A` đều thỏa `m ≤ β`. Kết hợp với điều kiện `β` là cận dưới của `A`,
đây là đặc trưng của cận dưới lớn nhất. Các điều kiện của tiểu mục được giữ nguyên.

Chứng minh: `calculus.Chapter02.Section01.greatestLowerBound_definition`.

<a id="c02-s01-proposition-003p01"></a>

### C02-S01-proposition-003.p01

Nguồn: `source/Ch2_dayso.tex` L214-L214; trạng thái gốc: **BLOCKED**.

Trong lời dẫn ở L212, sửa `α = inf(A)` thành `β = inf(A)`.
Giữ giả thiết `A` không rỗng và bị chặn dưới. Tiểu mục này yêu cầu
`β ≤ x` với mọi `x ∈ A`; điều kiện xấp xỉ trong tiểu mục kế tiếp được giữ riêng.

Hai điều kiện cùng nhau đặc trưng cho `IsGLB A β` dưới các giả thiết đã nêu.
Chứng minh: `calculus.Chapter02.Section01.greatestLowerBound_iff_epsilon`.

<a id="c02-s01-proposition-003p02"></a>

### C02-S01-proposition-003.p02

Nguồn: `source/Ch2_dayso.tex` L215-L215; trạng thái gốc: **BLOCKED**.

Dùng `β = inf(A)` trong lời dẫn ở L212, với `A` không rỗng và bị chặn dưới.
Tiểu mục này yêu cầu: với mỗi `ε > 0`, tồn tại `x ∈ A` sao cho `x < β + ε`.
Nhân chứng `x` được phép phụ thuộc vào `ε`.

Đây là điều kiện xấp xỉ, được dùng cùng điều kiện `β` là cận dưới của `A`.
Chứng minh: `calculus.Chapter02.Section01.greatestLowerBound_iff_epsilon`.

<a id="c02-s01-remark-004"></a>

### C02-S01-remark-004

Nguồn: `source/Ch2_dayso.tex` L237-L241; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Với tập A⊆ℝ không rỗng, bị chặn trên và bị chặn dưới, ta có `sup(-A)=-inf(A)` và `inf(-A)=-sup(A)`. Với A⊆B, A không rỗng và các cận thực cần thiết tồn tại, ta có `sup(A)≤sup(B)` và `inf(B)≤inf(A)`.

Các đẳng thức và bất đẳng thức này được hiểu trong ℝ, dưới các giả thiết bị chặn thích hợp. Quy ước `sup(∅)=-∞`, `inf(∅)=+∞` được xét riêng trong số thực mở rộng. Không gán một cận trên bé nhất hoặc cận dưới lớn nhất thực cho tập rỗng hay tập không bị chặn; các khái niệm thực được biểu diễn bằng `IsLUB` và `IsGLB`.

<a id="c02-s02-example-008proof-coefficients"></a>

### C02-S02-example-008.proof-coefficients

Nguồn: `source/Ch2_dayso.tex` L725-L731; trạng thái gốc: **FALSE AS STATED**.

**Bản sửa.** Thay phép tương đương đã khẳng định bằng:

`(β−α=7 ∧ αβ=−12) ↔ [(β=4 ∧ α=−3) ∨ (β=3 ∧ α=−4)]`.

Nói cách khác, hệ có đúng hai cặp nghiệm: (β,α)=(4,−3) hoặc (3,−4). Sau đó chọn cặp thứ nhất cho phép tính tiếp theo trong giáo trình. Giữ truy hồi và lựa chọn đã in; phân biệt việc chọn một nghiệm với việc liệt kê đầy đủ mọi nghiệm.

<a id="c02-s03-remark-001p04"></a>

### C02-S03-remark-001.p04

Nguồn: `source/Ch2_dayso.tex` L993-L999; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Thay `∃n∈N` bằng `∃n∈ℕ`. Dãy phân kì khi và chỉ khi với mọi a∈ℝ, tồn tại ε>0 sao cho với mọi số nguyên dương N, tồn tại chỉ số tự nhiên n≥N thỏa `|a_n-a|≥ε`.

Lời văn tại L998–999 xác định n là chỉ số của phần đuôi và N là một số. Thứ tự lượng từ là: ε được chọn sau a, còn n được chọn sau a, ε và N.

<a id="c02-s03-example-005proof-error-equality"></a>

### C02-S03-example-005.proof-error-equality

Nguồn: `source/Ch2_dayso.tex` L1016-L1016; trạng thái gốc: **FALSE AS STATED**.

**Bản sửa.** Tại L1016, thay `|a_n-1|=2/n` bằng `|a_n-1|≤2/n`. Giữ giá trị hữu tỉ chính xác của a_n, các cận ε còn lại và kết luận hội tụ.

<a id="c02-s03-example-006proof-strict-error"></a>

### C02-S03-example-006.proof-strict-error

Nguồn: `source/Ch2_dayso.tex` L1032-L1032; trạng thái gốc: **FALSE AS STATED**.

**Bản sửa.** Trong nhánh chọn chỉ số lẻ với a≥0, thay 1+a>1 bằng 1+a≥1. Với n=2N+1, sai số chính xác vẫn là `|(-1)^n-a|=1+a≥1`. Nhánh chọn chỉ số chẵn với a<0 giữ bất đẳng thức >1.

Giữ các cách chọn chỉ số chẵn, lẻ và ε=1. Dấu bằng tại a=0 phù hợp với tiêu chuẩn phân kì.

<a id="c02-s04-theorem-005proof-sign-interval"></a>

### C02-S04-theorem-005.proof-sign-interval

Nguồn: `source/Ch2_dayso.tex` L1434-L1434; trạng thái gốc: **FALSE AS STATED**.

**Bản sửa.** Thay `-M a_n≤a_n b_n≤M a_n` bằng `-M|a_n|≤a_n b_n≤M|a_n|`. Vì |a_n|→0, định lí kẹp vẫn cho a_n b_n→0.

Giữ M>0 và |b_n|≤M tại mọi chỉ số của giáo trình. Chỉ thêm trị tuyệt đối ở những vị trí mà dấu của thừa số a_n ảnh hưởng chiều bất đẳng thức.

<a id="c02-s05-theorem-001proof-strict-reciprocal-bound"></a>

### C02-S05-theorem-001.proof-strict-reciprocal-bound

Nguồn: `source/Ch2_dayso.tex` L1679-L1684; trạng thái gốc: **FALSE AS STATED**.

**Bản sửa.** Thay dấu ngặt đầu tiên tại L1679 và L1684 bằng ≤:

`|1/b_n-1/b|≤2|b_n-b|/b²`.

So sánh cuối với ε vẫn ngặt, nhờ `|b_n-b|<b²ε/2`. Giữ b≠0, b_n≠0 và cận |b_n|>|b|/2 trên phần đuôi. Cận mẫu yếu hơn, không ngặt, cũng đủ cho bất đẳng thức đã sửa và cho phép sai số bằng 0.

<a id="c02-s05-exercise-006"></a>

### C02-S05-exercise-006

Nguồn: `source/Ch2_dayso.tex` L1848-L1850; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Nếu a_n≠0 với mọi n≥1 và `lim_(n→∞)|a_(n+1)/a_n|=ℓ<1`, thì a_n→0.

Loại kí tự Ư không được định nghĩa và chọn tỉ số hai số hạng kế tiếp. Tỉ số này có được bằng phép đổi chỉ số từ tỉ số với số hạng trước tại n≥2; không lấy giá trị hoặc mở rộng a_0.

<a id="c02-s06-example-005proof-strict-geometric-bound"></a>

### C02-S06-example-005.proof-strict-geometric-bound

Nguồn: `source/Ch2_dayso.tex` L1946-L1946; trạng thái gốc: **FALSE AS STATED**.

**Bản sửa.** Thay cận sai tại L1946 bằng cận đầy đủ

`(1+1/n)^n≤exp(1)<3`, với mọi n≥1.

Cận này thay bước ước lượng tổng hình học và vẫn cho kết luận bị chặn trên.

<a id="c02-s07-exercise-002"></a>

### C02-S07-exercise-002

Nguồn: `source/Ch2_dayso.tex` L2163-L2165; trạng thái gốc: **FALSE AS STATED**.

**Rút phát biểu và giữ kết luận từ dữ kiện gốc.** Giữ x_0=y_0=0 và đúng truy hồi đã in. Khi đó x_n=y_n=0 với mọi n, nên `x_n²-2y_n²=0`. Các yêu cầu giá trị bằng ±1 và `x_n/y_n→sqrt(2)` được rút: thương không xác định tại mọi chỉ số của giáo trình.

Xem [bài thay thế](#hai-bai-thay-the).

<a id="c02-s07-exercise-004"></a>

### C02-S07-exercise-004

Nguồn: `source/Ch2_dayso.tex` L2172-L2176; trạng thái gốc: **FALSE AS STATED**.

**Bản sửa.** Nếu x_n>0 với mọi n≥1 và x_n→a, với a>0, thì cả hai dãy

`y_n=(x_1+…+x_n)/n`, `z_n=n/(1/x_1+…+1/x_n)`

đều hội tụ về a.

<a id="c02-s08-theorem-006"></a>

### C02-S08-theorem-006

Nguồn: `source/Ch2_dayso.tex` L2455-L2457; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Nếu a_n>0 với mọi n≥1 và `lim_(n→∞) a_(n+1)/a_n = ℓ>1`, thì a_n→+∞.

Loại kí tự Ư và dùng tỉ số với số hạng kế tiếp. Việc chọn số hạng làm mốc cho cận trong chứng minh được sửa riêng ở mục `C02-S08-theorem-006.proof-initial-anchor`.

<a id="c02-s08-theorem-006proof-initial-anchor"></a>

### C02-S08-theorem-006.proof-initial-anchor

Nguồn: `source/Ch2_dayso.tex` L2465-L2465; trạng thái gốc: **FALSE AS STATED**.

**Bản sửa.** Sau khi có cận tỉ số chỉ từ ngưỡng N trở đi, lấy a_N làm mốc:

`a_(N+k)≥a_N s^k`, với k≥0 và `s=(ℓ+1)/2>1`.

Không kéo cận ngược về a_1. Có thể dùng dấu > khi k≥1 nếu mỗi bước trên phần đuôi đều ngặt; bản không ngặt đã đủ suy ra a_n→+∞. Giữ ngưỡng N đã chứng minh và nêu rõ phép dịch chỉ số. Tại k=0, dùng ≥ để bao gồm đẳng thức ở số hạng làm mốc.

<a id="c02-s10-example-001proof-repeated-index"></a>

### C02-S10-example-001.proof-repeated-index

Nguồn: `source/Ch2_dayso.tex` L2683-L2683; trạng thái gốc: **FALSE AS STATED**.

**Bản sửa.** Thay 1/n thứ hai trong `|1/n-1/n|` bằng 1/m. Khi đó

`|a_n-a_m|=|1/n-1/m|≤1/n+1/m`.

Cận ε trong chứng minh Cauchy suy ra với m,n≥N≥1. Chỉ sửa chỉ số bị lặp; giữ a_n=1/n và kết luận Cauchy.

<a id="c02-s10-exercise-013"></a>

### C02-S10-exercise-013

Nguồn: `source/Ch2_dayso.tex` L2881-L2883; trạng thái gốc: **FALSE AS STATED**.

**Bản sửa.** Bổ sung giả thiết dãy có giá trị tự nhiên là dãy Cauchy. Khi đó tồn tại các số tự nhiên dương a,N sao cho x_n=a với mọi n≥N.

<a id="c02-s10-exercise-014"></a>

### C02-S10-exercise-014

Nguồn: `source/Ch2_dayso.tex` L2885-L2886; trạng thái gốc: **FALSE AS STATED**.

**Bản sửa.** Cho a>1. Nếu `|x_(k+1)-x_k|≤1/a^k` với mọi k≥1 thì dãy thực hội tụ.

Thay cận hằng `1/a` bằng cận hình học `1/a^k`.

<a id="c02-s11-prose-l2937"></a>

### C02-S11-prose-L2937

Nguồn: `source/Ch2_dayso.tex` L2937-L2937; trạng thái gốc: **FALSE AS STATED**.

**Bản sửa.** Giả sử A là tập số thực mở rộng, có một cận trên thực hữu hạn, và phần hữu hạn `F={r∈ℝ:r∈A}` không rỗng. Khi đó F bị chặn trên và có cận trên bé nhất thực s, với `sup_extended(A)=s`. Trường hợp đối ngẫu yêu cầu một cận dưới thực hữu hạn và F không rỗng để có cận dưới lớn nhất thực. Giữ các định nghĩa khác về thứ tự, cận và phần tử lớn nhất, nhỏ nhất.

Điều kiện phần hữu hạn không rỗng được bổ sung vào từng khẳng định tồn tại cận thực. Chỉ giả thiết A không rỗng chưa đủ. Không dùng giá trị mặc định của `sSup` hoặc `sInf` trong ℝ cho một tập rỗng.

<a id="c02-s11-definition-001p05"></a>

### C02-S11-definition-001.p05

Nguồn: `source/Ch2_dayso.tex` L2947-L2947; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Ở trường hợp (e), khi A có cận trên thực và phần hữu hạn không rỗng, định nghĩa sup(A) là cận trên bé nhất thực của `A\{-∞}`. Trường hợp đối ngẫu của inf(A) yêu cầu cận dưới thực và phần hữu hạn không rỗng. Các trường hợp (a), (d) xử lý tập rỗng hoặc tập chỉ chứa đầu mút vô cùng; các trường hợp (b), (c) xử lý khi không có cận hữu hạn.

Bản sửa nêu rõ phạm vi của (e), không suy đoán thứ tự ưu tiên ngầm giữa các điều kiện chồng lấn. Với giả thiết mới về phần hữu hạn không rỗng, (e) không chồng lấn các trường hợp chỉ chứa đầu mút vô cùng ở (a), (d).

<a id="c02-s11-theorem-001proof-strict-tail-supremum"></a>

### C02-S11-theorem-001.proof-strict-tail-supremum

Nguồn: `source/Ch2_dayso.tex` L3151-L3151; trạng thái gốc: **FALSE AS STATED**.

**Đính chính vị trí.** Công thức sai nằm tại **L3148-L3148**. Vị trí L3151-L3151 của dòng dữ liệu lịch sử được giữ nguyên.

**Bản sửa.** Trong bất đẳng thức chọn số hạng, thay dấu ngặt phía trên bằng ≤:

`s_(n_(k-1)+1)-1/k<a_(n_k)≤s_(n_(k-1)+1)`.

Cận xấp xỉ phía dưới vẫn ngặt; định lí kẹp cho kết luận hội tụ.
Cận trên không ngặt đã được in tại L3147. L3151 là dòng trống.

<a id="c02-s11-exercise-008"></a>

### C02-S11-exercise-008

Nguồn: `source/Ch2_dayso.tex` L3386-L3387; trạng thái gốc: **FALSE AS STATED**.

**Bản sửa.** Giữ x_n≥0, y_n≥0 và x_n→x; bổ sung x>0. Khi đó, trong số thực mở rộng,

`limsup(x_n y_n)=x limsup(y_n)`.

Giới hạn dương loại đúng trường hợp vô định 0·∞. Không coi phép nhân thông thường 0·∞ trong phát biểu gốc là đã xác định.

<a id="chuong-3"></a>

## Chương 3

<a id="c03-s01-example-001p01"></a>

### C03-S01-example-001.p01

Nguồn: `source/Ch3_gioihanhamso.tex` L56-L56; trạng thái gốc: **FALSE AS STATED**.

Với hàm hằng f:D→ℝ, f(x)=c, đồ thị là {(x,c):x∈D}. Đồ thị bằng toàn bộ đường thẳng y=c chỉ khi D=ℝ. Bản sửa giữ miền D đã cho, không thêm giả thiết 0∈D.

<a id="c03-s01-exercise-007p01"></a>

### C03-S01-exercise-007.p01

Nguồn: `source/Ch3_gioihanhamso.tex` L233-L233; trạng thái gốc: **FALSE AS STATED**.

Giữ định nghĩa f⁺(x)=max(f(x),0) và f⁻(x)=min(f(x),0) của giáo trình. Bản sửa đổi dấu trừ thành dấu cộng: f=f⁺+f⁻ tại mọi điểm thuộc miền.

<a id="c03-s01-exercise-007p02"></a>

### C03-S01-exercise-007.p02

Nguồn: `source/Ch3_gioihanhamso.tex` L234-L234; trạng thái gốc: **FALSE AS STATED**.

Với phần âm f⁻=min(f,0), điều kiện đúng là f≤g khi và chỉ khi f⁺≤g⁺ và f⁻≤g⁻, theo thứ tự từng điểm. Bản sửa chỉ đổi chiều bất đẳng thức của phần âm.

<a id="c03-s01-exercise-010p01"></a>

### C03-S01-exercise-010.p01

Nguồn: `source/Ch3_gioihanhamso.tex` L259-L259; trạng thái gốc: **FALSE AS STATED**.

Bản sửa thay tập đích ℝ bằng [0,+∞), giữ miền ban đầu. Hàm √x:[0,+∞)→[0,+∞) là song ánh, với hàm ngược y↦y².

<a id="c03-s01-exercise-010p02"></a>

### C03-S01-exercise-010.p02

Nguồn: `source/Ch3_gioihanhamso.tex` L260-L260; trạng thái gốc: **FALSE AS STATED**.

Bản sửa thay tập đích ℝ bằng ℝ\{1}. Hàm x↦(x+1)/(x−1) là song ánh từ ℝ\{1} vào chính nó và là hàm ngược của chính nó. Chỉ xét x≠1, nên mẫu không bằng 0.

<a id="c03-s01-remark-004p01"></a>

### C03-S01-remark-004.p01

Nguồn: `source/Ch3_gioihanhamso.tex` L309-L309; trạng thái gốc: **FALSE AS STATED**.

Nếu T>0 là một chu kì chung của f,g trên cùng miền được giữ bởi phép dịch x↦x+T, thì T cũng là chu kì của f+g, λf và fg. Bản sửa nói về một chu kì chung, không khẳng định T là chu kì nhỏ nhất của tổng.

<a id="c03-s01-proof-l0500-rational-endpoint-split"></a>

### C03-S01-proof-L0500-rational-endpoint-split

Nguồn: `source/Ch3_gioihanhamso.tex` L500-L500; trạng thái gốc: **FALSE AS STATED**.

Bỏ bước khẳng định mọi số hữu tỉ t≤b+c đều có dạng r+s với r,s hữu tỉ, r≤b và s≤c: bước phân tích này sai tại biên. Thay chứng minh của mệnh đề cha (iii) bằng đẳng thức lũy thừa thực hợp lệ: với a>0 và b,c∈ℝ, a^{b+c}=a^b a^c.

<a id="c03-s01-prose-l0560"></a>

### C03-S01-prose-L0560

Nguồn: `source/Ch3_gioihanhamso.tex` L560-L561; trạng thái gốc: **FALSE AS STATED**.

Theo bảng miền xác định của giáo trình, mọi đồ thị x^α đều chứa (1,1). Nếu α là số nguyên dương, đồ thị còn chứa (0,0). Số mũ dương không nguyên có miền (0,+∞), còn số mũ âm cũng loại 0. Bản sửa không mở rộng hàm tại 0.

<a id="c03-s01-prose-l0884"></a>

### C03-S01-prose-L0884

Nguồn: `source/Ch3_gioihanhamso.tex` L884-L886; trạng thái gốc: **FALSE AS STATED**.

Bản sửa đổi miền của secant từ (0,π)\{π/2} thành [0,π]\{π/2}, giữ tập đích ℝ\(−1,1). Hàm ngược là y↦arccos(1/y). Hai đầu mút 0,π cho các giá trị 1,−1, cần để hàm toàn ánh lên tập đích đã in.

<a id="c03-s01-exercise-020"></a>

### C03-S01-exercise-020

Nguồn: `source/Ch3_gioihanhamso.tex` L1262-L1264; trạng thái gốc: **FALSE AS STATED**.

Với f:ℝ→ℝ, nếu f∘f tăng ngặt và f∘f∘f giảm không ngặt thì f giảm ngặt. Bản sửa chỉ bổ sung tính ngặt vào giả thiết của lần lặp thứ hai; giữ nguyên giả thiết giảm của lần lặp thứ ba.

<a id="c03-s02-example-004proof-absolute-equality"></a>

### C03-S02-example-004.proof-absolute-equality

Nguồn: `source/Ch3_gioihanhamso.tex` L1499-L1499; trạng thái gốc: **FALSE AS STATED**.

Bản sửa thêm −3 vào vế phải của dấu bằng thứ nhất. Với x≠1, đẳng thức đúng là |f(x)−3|=|(x³−1)/(x−1)−3|=|x+2|·|x−1|. Ước lượng ε–δ và kết luận f(x)→3 tại 1 vẫn giữ trên ℝ\{1}.

<a id="c03-s02-display-l1783"></a>

### C03-S02-display-L1783

Nguồn: `source/Ch3_gioihanhamso.tex` L1783-L1783; trạng thái gốc: **FALSE AS STATED**.

Bản sửa thay x₀<x<x+δ bằng x₀<x<x₀+δ. Với giả thiết x₀ là điểm tụ phải của D, giới hạn lim(x→x₀+)f(x)=+∞ tương đương điều kiện

∀M∈ℝ, ∃δ>0, ∀x∈D, x₀<x<x₀+δ ⇒ f(x)>M.

<a id="c03-s03-example-003proof-cosine-delta-restriction"></a>

### C03-S03-example-003.proof-cosine-delta-restriction

Nguồn: `source/Ch3_gioihanhamso.tex` L2190-L2190; trạng thái gốc: **FALSE AS STATED**.

Bản sửa bỏ điều kiện δ<π/2 trong bước chọn δ=ε. Bất đẳng thức toàn cục |cos x−cos a|≤|x−a| cho phép dùng δ=ε với mọi ε>0. Giữ kết luận cos x→cos a và bài toán sin x/x→1; không giả sử ε tùy ý luôn nhỏ hơn π/2.

<a id="c03-s03-exercise-012p01"></a>

### C03-S03-exercise-012.p01

Nguồn: `source/Ch3_gioihanhamso.tex` L2406-L2406; trạng thái gốc: **FALSE AS STATED**.

Bản sửa bổ sung a<b. Nếu f tăng không ngặt và bị chặn trên trên (a,b), thì giới hạn trái tại b tồn tại hữu hạn và bằng sup f((a,b)). Các kết quả tương ứng ở đầu mút dưới và trong trường hợp không bị chặn được xét riêng.

<a id="c03-s04-remark-002p02"></a>

### C03-S04-remark-002.p02

Nguồn: `source/Ch3_gioihanhamso.tex` L2503-L2503; trạng thái gốc: **FALSE AS STATED**.

Bản sửa bổ sung a∈D và a là điểm tụ của D. Khi đó, nếu f không có giới hạn hữu hạn theo định nghĩa của giáo trình khi x→a trong D, thì f không liên tục tại a. Giả thiết điểm tụ là cần thiết: mọi hàm đều liên tục tại một điểm cô lập thuộc miền, trong khi định nghĩa giới hạn của giáo trình không áp dụng tại đó.

<a id="c03-s04-exercise-003p04"></a>

### C03-S04-exercise-003.p04

Nguồn: `source/Ch3_gioihanhamso.tex` L2691-L2694; trạng thái gốc: **FALSE AS STATED**.

Bản sửa giữ hai công thức cos(πx/2), |x−1| và đổi điều kiện nhánh thứ hai từ x>0 thành x>1. Hàm bằng cos(πx/2) khi x≤1 và |x−1| khi x>1 liên tục tại mọi x∈ℝ; tại điểm ghép 1, cả hai giới hạn bằng 0.

Hai điều kiện phân nhánh đã in chồng lấn.

<a id="c03-s05-corollary-001"></a>

### C03-S05-corollary-001

Nguồn: `source/Ch3_gioihanhamso.tex` L2882-L2884; trạng thái gốc: **BLOCKED**.

Bản sửa chọn m là giá trị nhỏ nhất và M là giá trị lớn nhất. Nếu f liên tục trên [a,b], a<b, thì với mọi γ thỏa m≤γ≤M, có một điểm x∈[a,b] sao cho f(x)=γ. Bất đẳng thức không ngặt bao gồm trường hợp hàm hằng, khi m=M.

Thứ tự tên cực trị trong bản in có thể làm [m,M] rỗng khi m>M; khi ấy mệnh đề lượng hóa trên khoảng này không có giá trị γ nào cần xét. Vì vậy phát biểu gốc giữ **BLOCKED**, không bị phân loại lại thành **FALSE AS STATED** chỉ từ cách đọc khoảng rỗng.

<a id="c03-s05-remark-002"></a>

### C03-S05-remark-002

Nguồn: `source/Ch3_gioihanhamso.tex` L2918-L2923; trạng thái gốc: **FALSE AS STATED**.

Bản sửa thay “tăng” bằng “tăng ngặt” trong cả hai đoạn, giữ a<b và tính liên tục trên (a,b).

- Nếu f bị chặn trên và dưới, đặt c=inf f((a,b)), d=sup f((a,b)). Khi đó c<d, giới hạn tại a+ bằng c, giới hạn tại b− bằng d, miền giá trị chính xác là (c,d), và hàm ngược (c,d)→(a,b) liên tục.
- Nếu f bị chặn dưới nhưng không bị chặn trên, đặt c=inf f((a,b)). Giới hạn tại a+ bằng c, giới hạn tại b− bằng +∞, miền giá trị chính xác là (c,+∞), và hàm ngược (c,+∞)→(a,b) liên tục.

<a id="c03-s06-remark-001"></a>

### C03-S06-remark-001

Nguồn: `source/Ch3_gioihanhamso.tex` L3052-L3058; trạng thái gốc: **FALSE AS STATED**.

Bản sửa yêu cầu f(x)>0 trên một tập thuộc lọc đang xét và g(x)log f(x)→L∈ℝ. Khi đó f(x)^{g(x)}→exp(L). Hai giới hạn riêng của f,g hoặc nhãn dạng vô định không bảo đảm tích g(x)log f(x) có giới hạn. Điều kiện bổ sung cho phép xử lý các dạng 0^0, 1^∞ và ∞^0.

Giữ hướng tiếp cận đã cho: tại điểm hữu hạn, từ một phía hoặc tại vô cùng, với điều kiện điểm tụ hay miền không bị chặn tương ứng. Không khẳng định giới hạn lũy thừa thực tại cơ số không dương ngoài miền hợp lệ.

<a id="c03-s06-exercise-008p04"></a>

### C03-S06-exercise-008.p04

Nguồn: `source/Ch3_gioihanhamso.tex` L3184-L3184; trạng thái gốc: **BLOCKED**.

Bản sửa chọn cách đặt ngoặc (sin x)^{tan x}, xét x→π/2 từ cả hai phía trên miền tự nhiên D={x: sin x∈realPowerDomain(tan x) ∧ cos x≠0}. Miền này nhận π/2 làm điểm tụ và giới hạn bằng 1. Cách đọc sin(x^{tan x}) là một biểu thức khác, không được coi là cùng bài toán.

<a id="c03-s07-remark-004p01"></a>

### C03-S07-remark-004.p01

Nguồn: `source/Ch3_gioihanhamso.tex` L3296-L3296; trạng thái gốc: **BLOCKED**.

Nếu f là vô cùng bé trên hướng tiếp cận đã cho và f(x)≠0 trên một tập thuộc lọc, thì |1/f(x)|→+∞ trên cùng hướng tiếp cận. Bản sửa bổ sung điều kiện khác 0 để nghịch đảo xác định. “Vô cùng lớn” ở đây xét giá trị tuyệt đối, không khẳng định 1/f(x)→+∞.

Hướng tiếp cận phải thỏa điều kiện điểm tụ hoặc miền không bị chặn của giáo trình. Không dùng 1/0 làm giá trị của hàm: với hàm hằng 0, miền tự nhiên của nghịch đảo rỗng. Đây là trở ngại về miền xác định, không phải phản ví dụ số học từ phép chia mở rộng của Lean.

<a id="c03-s07-remark-005"></a>

### C03-S07-remark-005

Nguồn: `source/Ch3_gioihanhamso.tex` L3374-L3376; trạng thái gốc: **BLOCKED**.

Bản sửa giữ định nghĩa bậc α và tính duy nhất của α. Chỉ so sánh với các β mà φ^β xác định trên một tập thuộc cùng lọc tiếp cận, theo `EventuallyRealPowerDefinedAlong`.

- Với vô cùng bé: β<α ⇒ f=o(φ^β), còn α<β ⇒ φ^β=o(f).
- Với vô cùng lớn: β<α ⇒ φ^β=o(f), còn α<β ⇒ f=o(φ^β).

Miền và hướng tiếp cận vẫn phải thỏa điều kiện của giáo trình. Không lượng hóa vô điều kiện mọi β∈ℝ: cơ số âm có thể cho phép số mũ 3 nhưng không cho phép β=3/2 trên cùng miền. Giá trị mở rộng của lũy thừa thực trong mathlib không thay điều kiện miền này.

<a id="c03-s07-exercise-003p12"></a>

### C03-S07-exercise-003.p12

Nguồn: `source/Ch3_gioihanhamso.tex` L3498-L3498; trạng thái gốc: **BLOCKED**.

Đọc kí hiệu chưa được định nghĩa `artan` thành `arctan`. Hàm đã sửa là
`f(x) = x² arctan(x) / (x⁵ + x² + 1)` trên miền
`D = {x ∈ ℝ : x⁵ + x² + 1 ≠ 0}`. Khi `x → 0` qua `D \ {0}` từ hai phía,
phần chính là `x³`: hệ số bằng 1 và bậc bằng 3.

Mẫu số liên tục và bằng 1 tại 0, nên miền chứa một lân cận của 0.
Chứng minh:
`calculus.Chapter03.Section07ExercisesCubicLeadingParts.rational_arctangent_cubic_principal_part`.

<a id="c03-s08-prose-l3875"></a>

### C03-S08-prose-L3875

Nguồn: `source/Ch3_gioihanhamso.tex` L3875-L3875; trạng thái gốc: **BLOCKED**.

Nếu f liên tục đều trên D, A⊆D và A≠∅, thì hàm hạn chế trên A liên tục đều theo định nghĩa của giáo trình. Chính xác hơn, dưới hai giả thiết đầu, `NonemptyUniformContinuousOn A f` khi và chỉ khi `A.Nonempty`.

Định nghĩa của giáo trình yêu cầu miền không rỗng; riêng điều kiện ε–δ vẫn đúng trên tập rỗng.

<a id="c03-s08-exercise-014p02"></a>

### C03-S08-exercise-014.p02

Nguồn: `source/Ch3_gioihanhamso.tex` L3994-L3994; trạng thái gốc: **BLOCKED**.

Giữ f được cho trên [a,+∞), liên tục trên miền đó và có giới hạn hữu hạn tại +∞. Bản sửa thay kết luận liên tục đều “trên ℝ” bằng “trên [a,+∞)”, đúng miền đã cho. Không chọn thêm một phần mở rộng của f ngoài miền.

<a id="chuong-4"></a>

## Chương 4

<a id="c04-s01-prose-l0123"></a>

### C04-S01-prose-L0123

Nguồn: `source/Ch4_hamsokhavi.tex` L123-L123; trạng thái gốc: **FALSE AS STATED**.

**Bản sửa.** Hai chỗ gọi `s(t)` là quãng đường được thay bằng tọa độ có dấu; hiệu hai tọa độ là độ dời. Vận tốc trung bình có dấu là `[s(t₀+h)−s(t₀)]/h`. Khi giới hạn hữu hạn hai phía tồn tại, vận tốc tức thời có dấu bằng đạo hàm.

**Điều kiện và phạm vi.** `s : ℝ → ℝ`; vận tốc trung bình xét `h > 0`, còn giới hạn đạo hàm xét `h → 0` với `h ≠ 0`. Với chuyển động tùy ý, trị tuyệt đối độ dời giữa hai đầu không nhất thiết bằng tổng quãng đường.

<a id="c04-s01-remark-004"></a>

### C04-S01-remark-004

Nguồn: `source/Ch4_hamsokhavi.tex` L252-L254; trạng thái gốc: **BLOCKED**.

**Bản sửa.** `(h∘g∘f)′(x₀)=h′(g(f(x₀)))·g′(f(x₀))·f′(x₀)`.

**Điều kiện và phạm vi.** Giữ `f(I₁) ⊆ I₂` và `g(I₂) ⊆ I₃`. Ba hàm `f,g,h` khả vi lần lượt tại `x₀,f(x₀),g(f(x₀))`. Mỗi đạo hàm được lấy tại điểm tương ứng, không dùng chung một điểm đánh giá.

<a id="c04-s01-boxed_assertion-001p02"></a>

### C04-S01-boxed_assertion-001.p02

Nguồn: `source/Ch4_hamsokhavi.tex` L275-L275; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Quy tắc đạo hàm lũy thừa chia thành ba trường hợp: số mũ thực `α` trên `x > 0`; số mũ nguyên dương `n` trên ℝ, với quy ước đa thức `x^0 = 1`; số mũ nguyên không dương `k` trên `x ≠ 0`. Khi `n = 1`, đạo hàm tại 0 bằng 1.

**Điều kiện và phạm vi.** Không dùng lũy thừa thực với cơ số âm và số mũ không nguyên, hoặc biểu thức `0^0` chưa được định nghĩa trong sách. Quy ước đa thức là phần bổ sung của bản sửa; nguồn gốc giữ nguyên.

<a id="c04-s01-example-005p01"></a>

### C04-S01-example-005.p01

Nguồn: `source/Ch4_hamsokhavi.tex` L329-L343; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Với `n ∈ ℕ`, `n ≥ 1`, `k ∈ ℕ` và `x ∈ ℝ`, đạo hàm cấp `k` của `x^n` bằng `n!/(n−k)! · x^(n−k)` khi `k ≤ n`, và bằng 0 khi `k > n`. Thừa số lũy thừa bậc 0 bằng 1, kể cả tại `x = 0`. Đạo hàm cấp `n` vì thế bằng `n!`.

**Điều kiện và phạm vi.** Công thức tổng quát gồm cấp 0; các đạo hàm cấp cao của sách dùng cấp dương. Quy ước đa thức được nêu riêng, không thay đổi định nghĩa lũy thừa thực tổng quát.

<a id="c04-s01-exercise-005"></a>

### C04-S01-exercise-005

Nguồn: `source/Ch4_hamsokhavi.tex` L463-L465; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Giữ 27 công thức đúng trên miền xác định của chúng. Chỉ thay tiểu mục `02` của bảng bằng quy tắc lũy thừa đã sửa ở trên, với ba trường hợp theo số mũ.

**Điều kiện và phạm vi.** Mỗi đạo hàm xét tại điểm thuộc miền tự nhiên của hàm sơ cấp trong sách. Giữ mọi điều kiện về tham số, cơ số, nhánh hàm ngược và mẫu khác 0.

<a id="c04-s01-exercise-006p11"></a>

### C04-S01-exercise-006.p11

Nguồn: `source/Ch4_hamsokhavi.tex` L479-L479; trạng thái gốc: **BLOCKED**.

**Hai cách đọc được chọn.** Xét riêng `(tan x)^(sin x)` và `tan(x^(sin x))`.

**Điều kiện và phạm vi.** Cả hai xét `0 < x < π/2`. Cách thứ nhất có cơ số tan dương. Cách thứ hai có cơ số `x` dương và `x^(sin x) ∈ (0,π/2)`, nên không gặp cực của tan. Hai cách đọc này không được coi là khôi phục ý định của tác giả.

<a id="c04-s01-exercise-013p08"></a>

### C04-S01-exercise-013.p08

Nguồn: `source/Ch4_hamsokhavi.tex` L592-L596; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Chọn `a,b ∈ ℝ`, `a ≥ 1`, đặt `f(0)=0`, `f(x)=bx` khi `x<0`, và `f(x)=x^a exp(−x²)` khi `x>0`. Hàm khả vi tại 0 khi và chỉ khi `b=1` nếu `a=1`, hoặc `b=0` nếu `a>1`. Trong mỗi trường hợp khả vi, đạo hàm bằng `b`. Cách đọc với `a` nguyên dương được ghi riêng.

**Điều kiện và phạm vi.** Lũy thừa thực chỉ dùng cơ số dương; giá trị 0 tại tâm là mở rộng liên tục được chọn rõ. Với số mũ tự nhiên `n≥1`, không cần mở rộng lũy thừa thực. Bài chỉ yêu cầu khả vi tại 0, không yêu cầu trơn toàn cục.

<a id="c04-s01-exercise-026"></a>

### C04-S01-exercise-026

Nguồn: `source/Ch4_hamsokhavi.tex` L690-L692; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Bổ sung `f(I) ⊆ I` vào phương trình `f′=g∘f`. Nếu `f` khả vi trên khoảng mở `I` và `g` trơn trên `I`, thì `f` trơn trên `I`.

**Điều kiện và phạm vi.** `I=(a,b)`, với `a<b` theo quy ước của sách; `MapsTo f I I` và phương trình đúng tại mọi `x∈I`. Giữ nghĩa trơn của sách đối với `g`; không giả sử trước rằng `f` trơn.

<a id="c04-s02-example-001"></a>

### C04-S02-example-001

Nguồn: `source/Ch4_hamsokhavi.tex` L764-L774; trạng thái gốc: **FALSE AS STATED**.

**Bản sửa.** Thay `1/30` bằng `1/300` và `301/30` bằng `3001/300`. Căn bậc ba thực có đạo hàm `1/300` tại 1000. Sai số xấp xỉ tuyến tính tại 1001 nhỏ hơn `2·10^-6`.

**Điều kiện và phạm vi.** Hai đối số 1000 và 1001 đều dương, nên không có sự mơ hồ về nhánh căn. Đây là xấp xỉ cấp một, không phải đẳng thức với giá trị căn vô tỉ.

<a id="c04-s02-display-l0793"></a>

### C04-S02-display-L0793

Nguồn: `source/Ch4_hamsokhavi.tex` L793-L797; trạng thái gốc: **BLOCKED**.

**Bản sửa.** `d²y(t)=[f″(φ(t))(φ′(t))²+f′(φ(t))φ″(t)]dt²`, hay `f″(x)dx²+f′(x)d²x`.

**Điều kiện và phạm vi.** `f` và `φ` khả vi hai lần trên các miền mở tương ứng, với `MapsTo φ I J`. Số gia vi phân `dt` giữ cố định. Công thức dùng đạo hàm cấp hai của hàm hợp.

<a id="c04-s02-display-l0807"></a>

### C04-S02-display-L0807

Nguồn: `source/Ch4_hamsokhavi.tex` L807-L807; trạng thái gốc: **FALSE AS STATED**.

**Bản sửa.** Trên nhánh có hàm ngược cục bộ, `y″ₓ=[φ′ψ″−φ″ψ′]/(φ′)^3`. Mẫu in trong sách được thay bằng `(φ′(t))³`.

**Điều kiện và phạm vi.** `φ,ψ` khả vi hai lần trên `(a,b)`, với `φ′≠0` trên khoảng này. Hàm `g` là hàm ngược cục bộ, thỏa `LeftInvOn`; đồ thị được lấy đạo hàm là `ψ∘g` trên nhánh đó.

<a id="c04-s03-exercise-005"></a>

### C04-S03-exercise-005

Nguồn: `source/Ch4_hamsokhavi.tex` L1112-L1113; trạng thái gốc: **FALSE AS STATED**.

**Bản sửa.** Bổ sung `f(x)≠0` tại mọi `x∈[a,b]`. Khi đó có `c∈(a,b)` thỏa công thức tỉ số hàm mũ in trong sách.

**Điều kiện và phạm vi.** `a<b` theo quy ước khoảng của sách; `f` liên tục trên đoạn và khả vi trong nội khoảng. Không cần đạo hàm tại đầu mút. Điều kiện khác 0 gồm cả hai đầu; hàm âm trên toàn đoạn vẫn được phép.

<a id="c04-s03-exercise-020"></a>

### C04-S03-exercise-020

Nguồn: `source/Ch4_hamsokhavi.tex` L1174-L1175; trạng thái gốc: **FALSE AS STATED**.

**Rút yêu cầu.** Rút khẳng định tồn tại tổng có trọng số trong trường hợp tổng quát.

**Phản ví dụ.** Với `f=x²`, mọi điểm `xₖ∈(0,1)` đều có `xₖ/f′(xₖ)=1/2`. Tổng có trọng số bằng `2013·2014/4`, thay vì `2013·2007/2`.

Xem [bài thay thế](#hai-bai-thay-the).

<a id="c04-s03-remark-001"></a>

### C04-S03-remark-001

Nguồn: `source/Ch4_hamsokhavi.tex` L1253-L1255; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Tách trường hợp tại tâm thành `f(x₀)=Pₙ(x₀)`, với thừa số lũy thừa bậc 0 bằng 1. Không yêu cầu điểm `c` nằm giữa hai điểm trùng nhau, hoặc lấy đạo hàm cấp `n+1` tại đầu mút chỉ để nhân với 0.

**Điều kiện và phạm vi.** Ngoài tâm, giữ các giả thiết Taylor của sách. Đẳng thức đa thức tại tâm đúng với `f` tùy ý theo quy ước đa thức đã nêu; không thêm giả thiết đạo hàm tại đầu mút.

<a id="c04-s03-remark-003"></a>

### C04-S03-remark-003

Nguồn: `source/Ch4_hamsokhavi.tex` L1264-L1268; trạng thái gốc: **FALSE AS STATED**.

**Bản sửa.** Khôi phục thừa số `(x−x₀)^n` ở số hạng thứ `n`. Giữ phần dư chính xác và trị tuyệt đối sai số `|f^(n+1)(c)(x−x₀)^(n+1)|/(n+1)!` theo các giả thiết Taylor in trong sách.

**Điều kiện và phạm vi.** `n≥1`, `x,x₀` thuộc đoạn đóng. Khi `x≠x₀`, điểm `c` nằm giữa hai điểm; tại tâm dùng đẳng thức đã sửa riêng. Giữ các giả thiết khả vi và liên tục của nguồn, không yêu cầu C^(n+1) toàn cục.

<a id="c04-s03-display-l1287eq03"></a>

### C04-S03-display-L1287.eq03

Nguồn: `source/Ch4_hamsokhavi.tex` L1290-L1290; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Giữ công thức Maclaurin hữu hạn và `θ∈(0,1)`, nhưng ghi rõ `x>−1`. Đây là miền lớn nhất để toàn đoạn Taylor từ 0 đến `x` tránh cực.

**Phản ví dụ.** Chỉ giả thiết `x≠−1` chưa đủ: `n=1,x=−2` bác bỏ công thức cho `1/(1+x)`.

<a id="c04-s03-display-l1287eq04"></a>

### C04-S03-display-L1287.eq04

Nguồn: `source/Ch4_hamsokhavi.tex` L1291-L1291; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Giữ công thức Maclaurin hữu hạn và `θ∈(0,1)`, nhưng ghi rõ `x<1`. Đây là miền lớn nhất để toàn đoạn Taylor từ 0 đến `x` tránh cực.

**Phản ví dụ.** Chỉ giả thiết `x≠1` chưa đủ: `n=1,x=2` bác bỏ công thức cho `1/(1−x)`.

**Chung cho hai công thức.** Kết quả được chứng minh với `n ≥ 1`. Tại tâm `x=0`, vẫn giữ `0<θ<1`.

<a id="c04-s04-theorem-003p03"></a>

### C04-S04-theorem-003.p03

Nguồn: `source/Ch4_hamsokhavi.tex` L1772-L1772; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Nếu đạo hàm dương ở cả hai phía của `x₀`, hoặc âm ở cả hai phía, trong một lân cận đã bỏ `x₀`, thì `x₀` không là điểm cực trị địa phương.

**Điều kiện và phạm vi.** Hàm liên tục tại `x₀` và khả vi trên lân cận thủng. Không thêm khả vi tại `x₀`. Nếu cho đạo hàm bằng 0, hàm hằng bác bỏ cách đọc rộng này.

<a id="c04-s04-proposition-002"></a>

### C04-S04-proposition-002

Nguồn: `source/Ch4_hamsokhavi.tex` L1955-L1957; trạng thái gốc: **FALSE AS STATED**.

**Bản sửa.** Bổ sung điều kiện `f` khả vi tại `x₀` hoặc có đạo hàm vô cùng hai phía tại đó theo định nghĩa của sách. Với khả vi hai lần ở hai phía và đạo hàm cấp hai đổi dấu ngặt, điểm trên đồ thị là điểm uốn theo định nghĩa của sách.

**Điều kiện và phạm vi.** Có `δ>0`; hàm khả vi hai lần trên hai khoảng mở hai bên. Giữ cả hai chiều đổi dấu: âm sang dương và dương sang âm. Định nghĩa điểm uốn còn yêu cầu tính chính quy tại điểm; chỉ liên tục không thay cho khả vi hoặc đạo hàm vô cùng.

<a id="c04-s04-example-010"></a>

### C04-S04-example-010

Nguồn: `source/Ch4_hamsokhavi.tex` L2002-L2191; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Chọn căn bậc ba thực có dấu `f(x)=signedCubeRoot(x³−3x+2)` trên ℝ. Các công thức `f′,f″` chỉ xét `x≠−2,1`. Tại 1, thương sai phân trái tiến `−∞`, thương sai phân phải tiến `+∞`: điểm nhọn có hướng tiếp tuyến đứng, nhưng không có đạo hàm vô cùng hai phía theo sách. Giữ vạch tung độ `∛4`, phù hợp với `f(−1)=∛4`.

**Điều kiện và phạm vi.** Dùng căn có dấu, không dùng `Real.rpow` tại đối số âm. Tiếp tuyến đứng về hình học khác đạo hàm vô cùng theo nguồn. Không coi vạch `∛4` là khẳng định giao điểm với trục tung; tên bổ đề cũ cũng không đủ để bác bỏ hình vẽ.

<a id="c04-s04-example-011"></a>

### C04-S04-example-011

Nguồn: `source/Ch4_hamsokhavi.tex` L2240-L2419; trạng thái gốc: **FALSE AS STATED**.

**Bản sửa.** Với `a>0`, giữ `X=a cos³t,Y=a sin³t`, sửa `Y′=+3a sin²t cos t` và hệ số góc ở điểm chính quy thành `−tan t`. Bốn điểm suy biến dùng giới hạn dây cung để xác định hướng và đường tiếp tuyến.

**Điều kiện và phạm vi.** `t∈ℝ`, với quy tắc rút tham số theo chu kì `2π` trong sách. Công thức hệ số góc đòi `sin t≠0` và `cos t≠0`. Tại điểm nhọn, vận tốc tham số bằng 0; không lấy thương `0/0` làm đạo hàm đồ thị.

<a id="c04-s04-display-l2539"></a>

### C04-S04-display-L2539

Nguồn: `source/Ch4_hamsokhavi.tex` L2539-L2544; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Với biểu diễn đã chọn `(x,y)=(r cosφ,r sinφ)`, bổ sung `r≥0` và `x≠0` trước khi kết luận `r=√(x²+y²)` và `tanφ=y/x`. Bán kính chuẩn không âm; góc còn cần được chọn theo góc phần tư.

**Điều kiện và phạm vi.** `r≥0` và `r cosφ≠0`, nên `cosφ≠0`. Phương trình tan không xác định duy nhất góc hoặc chọn bán kính có dấu. Các điểm trên trục tung cần chọn góc riêng, không dùng phép chia tại 0.

<a id="c04-s04-example-016"></a>

### C04-S04-example-016

Nguồn: `source/Ch4_hamsokhavi.tex` L2599-L2658; trạng thái gốc: **FALSE AS STATED**.

**Bản sửa.** Giữ đường cong `r=cos(2φ)` với bán kính có dấu, sửa điểm đã nêu thành `(0,−1)`, và phân biệt chu kì π của bán kính với chu kì `2π` của điểm Descartes. Dùng các phép đối xứng để dựng đủ bốn cánh và khảo sát chính đường cong này.

**Điều kiện và phạm vi.** `φ∈ℝ`, bán kính được phép âm. Thương đạo hàm làm hệ số góc chỉ dùng khi `X′≠0`; tại cực dùng vận tốc tham số khác 0 để xác định tiếp tuyến. Đường ba cánh `sin(3φ)` là hàm khác và không thay cho ví dụ này.

<a id="c04-s04-exercise-015p04"></a>

### C04-S04-exercise-015.p04

Nguồn: `source/Ch4_hamsokhavi.tex` L2779-L2779; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Với `a,b>0`, khảo sát `X=a/cos t,Y=b tan t` trên `D={t | 0≤t<2π và cos t≠0}`. Bỏ `t=π/2,3π/2` khỏi khoảng đã in.

**Điều kiện và phạm vi.** Giữ hai tham số dương và khoảng nửa mở của sách. Không dùng giá trị quy ước của sec hoặc tan tại cực. Không giả sử quỹ tích chỉ có một nhánh hypebol.

<a id="c04-s04-exercise-015p10"></a>

### C04-S04-exercise-015.p10

Nguồn: `source/Ch4_hamsokhavi.tex` L2785-L2785; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Chọn cách đọc hình học với hai bán kính `a>b>0`, và khảo sát cung hypocycloid theo công thức tham số đã in trên `0≤t≤2π`.

**Điều kiện và phạm vi.** `a,b∈ℝ`, `0<b<a`; giữ đoạn tham số đóng hữu hạn. Không giả sử `a/b` nguyên hoặc hữu tỉ, nên không khẳng định cung khép kín với mọi tỉ số thực. Giữ trường hợp `a=2b`, khi ảnh suy biến thành đoạn thẳng.

<a id="c04-s04-exercise-016p08"></a>

### C04-S04-exercise-016.p08

Nguồn: `source/Ch4_hamsokhavi.tex` L2800-L2800; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Chọn `a,n,m∈ℝ`, `m≠0`, khảo sát họ đường cong cực `r=a cos((n/m)φ)`, với `φ∈ℝ` và bán kính có dấu. Gọi đây là họ đường cong cực dạng cos; số cánh cần điều kiện riêng trên tham số.

**Điều kiện và phạm vi.** Giữ mọi tham số thực, trừ `m=0`, cùng các trường hợp suy biến `a=0` và `n=0`. Không ngầm giả sử tần số tự nhiên, nguyên hoặc hữu tỉ. Có thể bổ sung riêng trường hợp hoa với tần số nguyên, nhưng không thay nó cho toàn họ tham số thực.

<a id="c04-s04-exercise-023p04"></a>

### C04-S04-exercise-023.p04

Nguồn: `source/Ch4_hamsokhavi.tex` L2908-L2908; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Lợi nhuận có đơn vị đồng: `P(x)=R(x)−1000C(x)=−90000+3100x−24x²−x³/20`.

**Điều kiện và phạm vi.** Giữ dữ liệu chi phí `C` và giá bán `p` của sách. Chỉ đổi đơn vị chi phí một lần trước khi trừ. Tối ưu xét sản lượng `x≥0`; đẳng thức đa thức đúng với mọi `x∈ℝ`.

<a id="c04-s04-exercise-023p05"></a>

### C04-S04-exercise-023.p05

Nguồn: `source/Ch4_hamsokhavi.tex` L2909-L2909; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Dùng lợi nhuận đã đổi đơn vị ở mục trước. Sản lượng thực không âm tối ưu duy nhất là `x*=(-480+20√1041)/3`, với `55<x*<55.5`, nên làm tròn gần nhất thành 55. Sản lượng tự nhiên tối ưu duy nhất cũng là 55.

**Điều kiện và phạm vi.** `x≥0`. Nếu còn yêu cầu giá bán không âm, miền là `x≤350`; cả hai nghiệm tối ưu đều thỏa điều kiện này. Tối ưu trên số nguyên được chứng minh riêng, không chỉ suy từ phép làm tròn nghiệm thực.

<a id="c04-s04-exercise-024p01"></a>

### C04-S04-exercise-024.p01

Nguồn: `source/Ch4_hamsokhavi.tex` L2917-L2918; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Bổ sung mô hình cầu afin `p(x)=mx+b`. Trong lớp mô hình này, dữ kiện của sách xác định `p(x)=472000−400x`, đơn vị đồng.

**Điều kiện và phạm vi.** Với sản lượng thực không âm và giá không âm, miền là `0≤x≤1180`. Nếu chỉ xét giảm giá, miền là `180≤x≤1180`.

<a id="c04-s04-exercise-024p02"></a>

### C04-S04-exercise-024.p02

Nguồn: `source/Ch4_hamsokhavi.tex` L2919-L2919; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Theo mô hình cầu afin đã chọn, doanh thu là `R(x)=x p(x)=472000x−400x²`, đơn vị đồng.

**Điều kiện và phạm vi.** Dùng miền sản lượng ở `C04-S04-exercise-024.p01`. Đẳng thức `R=xp` đúng với mọi hàm cầu.

<a id="c04-s04-exercise-024p03"></a>

### C04-S04-exercise-024.p03

Nguồn: `source/Ch4_hamsokhavi.tex` L2920-L2920; trạng thái gốc: **BLOCKED**.

**Bản sửa.** Theo mô hình afin, sản lượng tối ưu duy nhất, cả thực lẫn nguyên, là 590. Giá bán là 236000 đồng, mức giảm giá 164000 đồng, và doanh thu lớn nhất 139240000 đồng.

**Điều kiện và phạm vi.** Sản lượng 590 thuộc cả miền giá không âm lẫn miền chỉ giảm giá. Không thêm điều kiện mức giảm phải là bội của 10000. Tối ưu trên miền thực và trên sản lượng nguyên được xét riêng.

<a id="hai-bai-thay-the"></a>

## Hai bài thay thế

Bài Pell thay thế dùng các dãy thực với chỉ số `n ≥ 0`:

$$
x_0 = y_0 = 1,\qquad
x_{n+1} = x_n + 2y_n,\qquad y_{n+1} = x_n + y_n.
$$

Các giá trị đầu đều đổi từ 0 thành 1; truy hồi của `x` dùng `y_n`.
Với mọi `n ≥ 0`, chứng minh cho `x_n ≥ 1`, `y_n ≥ n + 1` và

$$
x_n^2 - 2y_n^2 = (-1)^{n+1},\qquad
\left|\frac{x_n}{y_n} - \sqrt{2}\right| \le \frac{1}{y_n}.
$$

Do đó mẫu khác 0 và thương hội tụ về `√2`. Tính dương và việc mẫu tiến ra vô cực
được suy ra từ truy hồi. Xem [mô-đun Pell](../calculus/Chapter02/Section06PellReplacement.lean).

Bài tổng có trọng số giữ các giả thiết: `f : ℝ → ℝ` liên tục trên `[0, 1]`,
khả vi trên `(0, 1)`, `f(0) = 0` và `f(1) = 1`. Với mỗi số nguyên dương `n`,
tồn tại `0 < x₁ < … < xₙ < 1`, có `f′(xₖ) ≠ 0`, sao cho

$$
\sum_{k=1}^{n}\frac{k x_k}{f'(x_k)} = \frac{n(n+1)}{4}.
$$

Với `n = 2013`, tổng bằng `2013 · 2014 / 4`. Các điểm tăng ngặt và đạo hàm
khác 0 là kết luận về các điểm được chọn, không phải giả thiết thêm về `f`.
Chứng minh dùng định lí giá trị trung gian để chọn các đoạn, rồi dùng định lí
Cauchy với `g(t) = t²` để tính tổng. Xem
[mô-đun tổng có trọng số](../calculus/Chapter04/Section03WeightedSumReplacement.lean).
