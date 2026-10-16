# Hình thức hoá bằng Lean của Giáo trình Giải tích I (Lean formalization of *Calculus I*)

Các tệp trong repo này chứa bản hình thức hóa bằng Lean cuốn giáo trình *Giáo trình Giải tích I*. Bản hình thức hóa này nhằm diễn đạt lại nội dung nguyên tác một cách trung thành nhất có thể, đồng thời giới thiệu các tính năng và cú pháp của Lean.

Đồng hành về *Hình thức hoá bằng Lean cho Giải tích I* với hướng dẫn chi tiết hơn cho người mới bắt đầu được cung cấp tại [https://lean.giaitich.com](https://lean.giaitich.com).

Giấy phép: [LICENSE](https://github.com/madisondong/lean-formalization-calculus/blob/main/LICENSE).

Nguồn:

Bản giấy: *Giáo trình Giải tích I*, Nguyễn Thái An, Lê Thị Như Bích, Phạm Đình Đồng, Trần Thiện Tín, Nhà xuất bản Đại học Huế, 2025.

Bản online: [https://www.giaitich.com](https://www.giaitich.com).

## Biên dịch

Cài `elan`, Git và Python 3.9 trở lên, rồi chạy:

```sh
git clone https://github.com/madisondong/lean-formalization-calculus.git
cd lean-formalization-calculus
lake exe cache get
lake build
```

Dùng thư viện trong Lean:

```lean
import calculus
```

## Kiểm tra

Chạy tại thư mục gốc dự án:

```sh
bash scripts/check.sh
```

Lệnh này biên dịch thư viện, kiểm tra các mô-đun được nhập, phiên bản phụ thuộc
và tiên đề của các chứng minh. Mỗi lần chạy lưu nhật ký riêng trong
`.lake/verification/`; `CHECK_OK` xác nhận mọi bước đã đạt.
Danh sách phát biểu được phép dùng `sorry` nằm trong [mã kiểm tra](scripts/check_project.py).
Các chứng minh khác phải độc lập với những phát biểu này.

## Đối chiếu với giáo trình

| Chương, mục | Nội dung | Mã Lean |
| --- | --- | --- |
| 1.1 | Các phép toán trên các mệnh đề | [Đọc mã](calculus/Chapter01/Section01.lean) |
| 1.2 | Luật logic | [Đọc mã](calculus/Chapter01/Section02.lean) |
| 1.3 | Quy tắc suy luận | [Đọc mã](calculus/Chapter01/Section03.lean) |
| 1.4 | Tập hợp | [Đọc mã](calculus/Chapter01/Section04.lean) |
| 1.5 | Ánh xạ | [Đọc mã](calculus/Chapter01/Section05.lean) |
| 2.1 | Một số tính chất của tập số thực | [Đọc mã](calculus/Chapter02/Section01.lean) |
| 2.2 | Định nghĩa dãy số | [Đọc mã](calculus/Chapter02/Section02.lean) |
| 2.3 | Giới hạn của dãy số | [Đọc mã](calculus/Chapter02/Section03.lean) |
| 2.4 | Một số tính chất của dãy số hội tụ | [Đọc mã](calculus/Chapter02/Section04.lean) |
| 2.5 | Các phép toán trên các dãy số hội tụ | [Đọc mã](calculus/Chapter02/Section05.lean) |
| 2.6 | Dãy số đơn điệu | [Đọc mã](calculus/Chapter02/Section06.lean) |
| 2.7 | Dãy số có giới hạn bằng vô cùng | [Đọc mã](calculus/Chapter02/Section07.lean) |
| 2.8 | Định lí Cantor và Định lí Bolzano-Weierstrass | [Đọc mã](calculus/Chapter02/Section08.lean) |
| 2.9 | Dãy Cauchy | [Đọc mã](calculus/Chapter02/Section09.lean) |
| 2.10 | Giới hạn trên, giới hạn dưới | [Đọc mã](calculus/Chapter02/Section10.lean) |
| 3.1 | Hàm số biến số thực | [Đọc mã](calculus/Chapter03/Section01.lean) |
| 3.2 | Giới hạn hàm số | [Đọc mã](calculus/Chapter03/Section02.lean) |
| 3.3 | Các tính chất của giới hạn hàm số | [Đọc mã](calculus/Chapter03/Section03.lean) |
| 3.4 | Tính liên tục | [Đọc mã](calculus/Chapter03/Section04.lean) |
| 3.5 | Các tính chất của hàm số liên tục | [Đọc mã](calculus/Chapter03/Section05.lean) |
| 3.6 | Tính liên tục của các hàm sơ cấp cơ bản | [Đọc mã](calculus/Chapter03/Section06.lean) |
| 3.7 | Vô cùng bé, vô cùng lớn, khử dạng vô định | [Đọc mã](calculus/Chapter03/Section07.lean) |
| 3.8 | Tính liên tục đều | [Đọc mã](calculus/Chapter03/Section08.lean) |
| 4.1 | Khái niệm đạo hàm | [Đọc mã](calculus/Chapter04/Section01Derivatives.lean) |
| 4.2 | Vi phân | [Đọc mã](calculus/Chapter04/Section02.lean) |
| 4.3 | Các định lí cơ bản về hàm khả vi | [Đọc mã](calculus/Chapter04/Section03.lean) |
| 4.4 | Một số ứng dụng của phép tính vi phân | [Đọc mã](calculus/Chapter04/Section04.lean) |

Xem [thuật ngữ Việt–Anh–Lean](https://github.com/madisondong/lean-formalization-calculus/blob/main/docs/glossary-vi-en.md) và [đính chính giáo trình](https://github.com/madisondong/lean-formalization-calculus/blob/main/docs/errata.md).
