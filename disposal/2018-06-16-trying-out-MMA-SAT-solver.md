---
layout: post
title: 试用Mathematica SAT solver
key: trying-out-MMA-SAT-solver
tags:
  - 技术
  - Mathematica
---

本文将记录我对MMA的SAT求解器和FindInstance函数的试用过程，作为学习用于求解SMT问题的z3求解器的前导知识。

<!--more-->

---

## SatisfiabilityInstances(SAT solver)

In[1]:=$$\text{SatisfiabilityInstances}[a\Rightarrow \neg b,\{a,b\},4]$$

Out[1]=$$\left(
\begin{array}{cc}
 \text{True} & \text{False} \\
 \text{False} & \text{True} \\
 \text{False} & \text{False} \\
\end{array}
\right)$$

即，Out[1]中的三种布尔值组合可以使$$a\Rightarrow \neg b=True$$

这样的逻辑表达式处理是形式逻辑的基础之一，与“真实之月”企划的语言哲学部分有些关系。基本上《逻辑哲学论》中一大块难点都是来自这里...

---

回到SAT solver上来。

将$$a\veebar b\veebar c\veebar d\veebar e$$作DNF展开之后可以得到$$(a\land b\land c\land d\land e)\lor (a\land b\land c\land \neg d\land \neg e)\lor (a\land b\land \neg c\land d\land \neg e)\lor (a\land b\land \neg c\land \neg d\land e)\lor (a\land \neg b\land c\land d\land \neg e)\lor (a\land \neg b\land c\land \neg d\land e)\lor (a\land \neg b\land \neg c\land d\land e)\lor (a\land \neg b\land \neg c\land \neg d\land \neg e)\lor (\neg a\land b\land c\land d\land \neg e)\lor (\neg a\land b\land c\land \neg d\land e)\lor (\neg a\land b\land \neg c\land d\land e)\lor (\neg a\land b\land \neg c\land \neg d\land \neg e)\lor (\neg a\land \neg b\land c\land d\land e)\lor (\neg a\land \neg b\land c\land \neg d\land \neg e)\lor (\neg a\land \neg b\land \neg c\land d\land \neg e)\lor (\neg a\land \neg b\land \neg c\land \neg d\land e)$$，当然丧心病狂一点也可以做成$$(a\Rightarrow \neg ((b\Rightarrow \neg ((c\Rightarrow \neg ((d\Rightarrow \neg e)\Rightarrow \neg (\neg d\Rightarrow e)))\Rightarrow \neg (\neg c\Rightarrow \neg ((d\Rightarrow e)\Rightarrow \neg (\neg d\Rightarrow \neg e)))))\Rightarrow \neg (\neg b\Rightarrow \neg ((c\Rightarrow \neg ((d\Rightarrow e)\Rightarrow \neg (\neg d\Rightarrow \neg e)))\Rightarrow \neg (\neg c\Rightarrow \neg ((d\Rightarrow \neg e)\Rightarrow \neg (\neg d\Rightarrow e)))))))\Rightarrow \neg (\neg a\Rightarrow \neg ((b\Rightarrow \neg ((c\Rightarrow \neg ((d\Rightarrow e)\Rightarrow \neg (\neg d\Rightarrow \neg e)))\Rightarrow \neg (\neg c\Rightarrow \neg ((d\Rightarrow \neg e)\Rightarrow \neg (\neg d\Rightarrow e)))))\Rightarrow \neg (\neg b\Rightarrow \neg ((c\Rightarrow \neg ((d\Rightarrow \neg e)\Rightarrow \neg (\neg d\Rightarrow e)))\Rightarrow \neg (\neg c\Rightarrow \neg ((d\Rightarrow e)\Rightarrow \neg (\neg d\Rightarrow \neg e)))))))$$（只用推出和否关系的IMPLIES展开）。布尔函数真是个坑爹玩意.....（[注1](#1)）

让MMA来求解一下这个

In[2]:=$$\text{SatisfiabilityInstances}[\text{BooleanConvert}[a\veebar b\veebar c\veebar d\veebar e,\text{IMPLIES}],\{a,b,c,d,e\},10]$$

Out[2]=$$\left(
\begin{array}{ccccc}
 \text{True} & \text{True} & \text{True} & \text{True} & \text{True} \\
 \text{True} & \text{True} & \text{True} & \text{False} & \text{False} \\
 \text{True} & \text{True} & \text{False} & \text{True} & \text{False} \\
 \text{True} & \text{True} & \text{False} & \text{False} & \text{True} \\
 \text{True} & \text{False} & \text{True} & \text{True} & \text{False} \\
 \text{True} & \text{False} & \text{True} & \text{False} & \text{True} \\
 \text{True} & \text{False} & \text{False} & \text{True} & \text{True} \\
 \text{True} & \text{False} & \text{False} & \text{False} & \text{False} \\
 \text{False} & \text{True} & \text{True} & \text{True} & \text{False} \\
 \text{False} & \text{True} & \text{True} & \text{False} & \text{True} \\
\end{array}
\right)$$

易如反掌。

---

## FindInstance

直接上例子。

求方程组的一个解：

In[3]:=`FindInstance[x^2 + y^2 + z^2 == -1 && z^2 == 2 x - 5 y, {x, y, z}]`

Out[3]=$$\left\{\left\{x\to 0,y\to \frac{1}{2} \left(5-\sqrt{21}\right),z\to -i \sqrt{\frac{5}{2} \left(5-\sqrt{21}\right)}\right\}\right\}$$

求三个整数解：

In[4]:=`FindInstance[x^2 - 3 y^2 == 1 && 10 < x < 100, {x, y}, Integers,3]`

Out[4]=$$\{\{x\to 97,y\to 56\},\{x\to 97,y\to -56\},\{x\to 26,y\to -15\}\}$$

求满足公式的布尔变量值：

In[5]:=$$\text{FindInstance}[(a\veebar b\veebar c\veebar d)\land (a\lor b)\land \neg (c\lor d),\{a,b,c,d\},\mathbb{B}]$$

Out[5]=$$\{\{a\to \text{False},b\to \text{True},c\to \text{False},d\to \text{False}\}\}$$

求几何区域中的点：

In[6]:=$$\text{FindInstance}\left[\{x,y\}\in \text{InfiniteLine}\left[\{\{0, 0\}, \{2, 1\}\}\right]\land \{x,y\}\in \text{Circle}[],\{x,y\},2\right]$$

Out[6]=$$\left\{\left\{x\to -\frac{2}{\sqrt{5}},y\to -\frac{1}{\sqrt{5}}\right\},\left\{x\to \frac{2}{\sqrt{5}},y\to \frac{1}{\sqrt{5}}\right\}\right\}$$

这里其实求了一个圆和一条直线的两个交点的坐标。

---

## SAT solver 实用案例

证明下列statement不是一个[同义反复](#2)：

In[7]:=$$\text{SatisfiabilityInstances}[(b\land ((a\land \neg (b\lor (a\land c)))\lor b\lor (a\land c)))\lor \neg a\lor \neg ((a\land \neg (b\lor (a\land c)))\lor b\lor (a\land c)),\{a,b,c\}]$$

Out[7]=$$\{\{a\to \text{True},b\to \text{False},c\to \text{True}\}\}$$

## 结语

MMA赛高！

（怎么学着学着就开始吹MMA了）

---

## 注释

<span id="1">**注1**：在逻辑学中，推出关系$$a\Rightarrow b$$同样是一个函数，等价于$$\neg a\lor b$$。这也就是“从False中可以推出一切”的原因。</span>

值得注意的是，“等价于”也是一个布尔函数。$$(e_1 \Longleftrightarrow e_2 \Longleftrightarrow ...)\Longleftrightarrow(\left(e_1\land e_2\land \cdots \right)\lor \left(\neg e_1\land \neg e_2\land \cdots \right))$$

这打开了一个新世界的大门。

<span id="2">**注2**：即“重言式”，始终为True的布尔函数,如$$a=a$$。与之相反的是“矛盾式”，始终为False，如$$a= \neg a$$。这两者按路德维希·维特根斯坦的说法，分别不占用逻辑空间、填满了整个逻辑空间，是唯一先天能够得到真值函项取值的命题。它们什么也没“说”，但勾勒出了语言和逻辑的界限。</span>