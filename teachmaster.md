# Coq 定理证明入门：简单证明与定义

## 整数算数运算与大小比较

算术与数量之间的大小关系是日常生活中最常见的数学概念。我们可以用数描述物体的数量、几何图形的长度与面积、人的年龄等等。作为Coq验证工具的入门篇，这一章将介绍如何使用Coq表达一些简单的数量关系，并证明一些简单的性质。

### 鸡兔同笼问题

大约在1500年前，《孙子算经》一书中记载了这样一个有趣的问题：今有雉兔同笼，上有三十五头，下有九十四足，问雉兔各几何？这就是著名的鸡兔同笼问题。

如果用C表示鸡（Chicken）的数量，用R表示兔（Rabbit）的数量，那么这一问题中的数量关系就可以表示为：

- `C + R = 35`
- `2 * C + 4 * R = 94`

进而可以求解得知 `C = 23`（也可以求解得到 `R = 12`）。这一推理过程可以在Coq中表示成为下面命题。

```coq
Fact chickens_and_rabbits: forall C R: Z,
  C + R = 35 ->
  2 * C + 4 * R = 94 ->
  C = 23.
```

**证明：**
```coq
Proof. lia. Qed.
```

在Proof和Qed之间的`lia`指令是证明脚本，表示使用线性整数运算自动证明。

### 幼儿园师生问题

下面这个例子选自熊斌教授所著《奥数教程》的小学部分：幼儿园的小朋友去春游，有男孩、女孩、男老师与女老师共16人，已知小朋友比老师人数多，但是女老师比女孩人数多，女孩又比男孩人数多，男孩比男老师人数多，请证明幼儿园只有一位男老师。

```coq
Fact teachers_and_children: forall MT FT MC FC: Z,
  MT > 0 ->
  FT > 0 ->
  MC > 0 ->
  FC > 0 ->
  MT + FT + MC + FC = 16 ->
  MC + FC > MT + FT ->
  FT > FC ->
  FC > MC ->
  MC > MT ->
  MT = 1.
Proof. lia. Qed.
```



### 非线性运算性质

除了线性性质之外，Coq中还可以证明一些更复杂的性质。例如下面就可以证明，任意两个整数的平方和总是大于它们的乘积。

```coq
Fact sum_of_sqr1: forall x y: Z,
  x * x + y * y >= x * y.
Proof. nia. Qed.
```

`nia`指令表示非线性整数运算求解。不过，`nia`与`lia`不同，后者能够保证关于线性运算的真命题总能被自动证明，但是有不少非线性的算数运算性质是`nia`无法自动验证的。

```coq
Fact sum_of_sqr2: forall x y: Z,
  x * x + y * y >= 2 * x * y.
Proof. Fail nia. Abort.
```

这时，我们需要编写证明脚本，给出中间证明步骤：

```coq
Fact sum_of_sqr2: forall x y: Z,
  x * x + y * y >= 2 * x * y.
Proof.
  intros.
  pose proof sqr_pos (x - y).
  nia.
Qed.
```

- `intros`：将待证明结论中的逻辑结构"对于任意整数x与y"移除，并在前提中加入"x与y是整数"这两条假设
- `pose proof`：对`x - y`使用标准库中的定理`sqr_pos`



## 函数与谓词

### 函数的定义

函数是一类重要的数学对象。例如，"加一"这个函数在Coq中可以定义为：

```coq
Definition plus_one (x: Z): Z := x + 1.
```

我们可以证明关于这个函数的一些简单性质：

```coq
Example One_plus_one: plus_one 1 = 2.
Proof. unfold plus_one. lia. Qed.

Example One_plus_one_plus_one: plus_one (plus_one 1) = 3.
Proof. unfold plus_one. lia. Qed.
```

更多函数的例子：

```coq
Definition square (x: Z): Z := x * x.

Example square_5: square 5 = 25.
Proof. unfold square. lia. Qed.

Definition smul (x y: Z): Z := x * y + x + y.

Example smul_ex1: smul 1 1 = 3.
Proof. unfold smul. lia. Qed.

Example smul_ex2: smul 2 3 = 11.
Proof. unfold smul. lia. Qed.
```

### 谓词的定义

在Coq中，可以通过定义类型为`Prop`的函数来定义谓词：

```coq
Definition nonneg (x: Z): Prop := x >= 0.
```

我们可以证明关于这个谓词的性质：

```coq
Fact nonneg_plus_one: forall x: Z,
  nonneg x -> nonneg (plus_one x).
Proof. unfold nonneg, plus_one. lia. Qed.

Fact nonneg_square: forall x: Z,
  nonneg (square x).
Proof. unfold nonneg, square. nia. Qed.
```



