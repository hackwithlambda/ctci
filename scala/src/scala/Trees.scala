package org.hackwithlambda.ctci

// This is AVL trees

case class Leaf[A <: Ordered[A]](data: A) extends Tree[A] {
  val height = 1
}
case class Branch[A <: Ordered[A]](data: A, left: Tree[A], right: Tree[A]) extends Tree[A] {
  val height = max(lt.height, rt.height) + 1
}

sealed abstract class Tree[A] {
  def toBalTree(sorteds: List[A]): Tree[A]
}


object TreeFunctions {
  def isBalanced(tree: Tree[A]): Boolean = tree match {
    case Leaf (_) => true
    case Branch (_, lt, rt) => Math.abs(lt.height - rt.height) <= 1
  }

}
