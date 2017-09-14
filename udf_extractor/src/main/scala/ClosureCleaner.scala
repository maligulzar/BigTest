//
//import java.io._
//import java.nio.channels.FileChannel
//import scala.collection.mutable
//import scala.collection.mutable.{Map, Set, Stack}
//import scala.language.existentials
//
//import org.apache.xbean.asm5.{ClassReader, ClassVisitor, MethodVisitor, Type}
//import org.apache.xbean.asm5.Opcodes._
//
//import org.apache.xbean.asm5.Type
//import org.apache.xbean.asm5.tree.ClassNode
//import org.apache.xbean.asm5.tree.LocalVariableNode
//import org.apache.xbean.asm5.tree.MethodNode
//
//import org.apache.spark.{CodeAnalyzer, SparkEnv, SparkException}
//import org.apache.spark.internal.Logging
//
//
//
///**
//  * A cleaner that renders closures serializable if they can be done so safely.
//  */
//
// class TypeFinderVisitor(output: mutable.HashMap[String, String]) extends ClassVisitor(ASM5) {
//  var myName: String = null
//
//  // TODO: Recursively find inner closures that we indirectly reference, e.g.
//  //   val closure1 = () = { () => 1 }
//  //   val closure2 = () => { (1 to 5).map(closure1) }
//  // The second closure technically has two inner closures, but this finder only finds one
//
//  override def visit(version: Int, access: Int, name: String, sig: String,
//                     superName: String, interfaces: Array[String]) {
//    myName = name
//  }
//
//  override def visitMethod(access: Int, name: String, desc: String,
//                           sig: String, exceptions: Array[String]): MethodVisitor = {
//    val thistype = Type.getArgumentTypes(desc)
//    val thisreturn = Type.getReturnType(desc)
//    val aname = thistype.map{s => println(s)}
//    val cname  = thisreturn.getClassName
//
//    new MethodVisitor(ASM5) {
//   //   override def visitParameterAnnotation(parameter: Int, desc: String, visible: Boolean){
//     //   Type.getArgumentTypes(desc).foreach(println)
//     // }
//      override def visitMethodInsn(
//                                    op: Int, owner: String, name: String, desc: String, itf: Boolean) {
//        val argTypes = Type.getArgumentTypes(desc)
//        if (op == INVOKESPECIAL && name == "<init>" && argTypes.length > 0
//          && argTypes(0).toString.startsWith("L") // is it an object?
//          && argTypes(0).getInternalName == myName) {
//
//        }
//      }
//    }
//  }
//}
// class ClosureCleaner extends Logging with CodeAnalyzer {
//
//
//   override def analyzeFunction(f: AnyRef){
//     getMethods(f.getClass).foreach(printMethod _ )
//     def printMethod(m:ScalaMethod) = {
//       print("**********************\n")
//       println (m.name+" => "+m.returnType.getClassName)
//       m.params.foreach(p =>
//         println (" "+ p.paraName+":"+p.paraType.getClassName))
//     print("**************************\n\n\n\n\n")
//     }
//   }
//
//
//   case class Param(paraName:String, paraType:Type)
//   case class ScalaMethod(name:String, returnType:Type, params:List[Param])
//
//   /**
//     * extracts the names, parameter names and parameter types of all methods of c
//     */
//   def getMethods(c:Class[_]):List[ScalaMethod] = {
//     val cl:ClassLoader = c.getClassLoader();
//     val t:Type = Type.getType(c);
//     val url:String = t.getInternalName() + ".class";
//     val is:InputStream = cl.getResourceAsStream(url);
//     if (is == null)
//       throw new IllegalArgumentException("""The class loader cannot
//                                         find the bytecode that defined the
//                                         class (URL: " + url + ")""");
//     val cn = new ClassNode();
//     val cr = new ClassReader(is);
//     cr.accept(cn, 0);
//     is.close();
//     val methods = cn.methods.asInstanceOf[java.util.List[MethodNode]];
//     var mList:List[ScalaMethod] = Nil
//     if (methods.size > 0) for (i <- 1 to methods.size) {
//       val m:MethodNode = methods.get(i-1)
//       val argTypes:Array[Type] = Type.getArgumentTypes(m.desc);
//       val paraNames = new java.util.ArrayList[String](argTypes.length)
//       val vars = m.localVariables.asInstanceOf[java.util.List[LocalVariableNode]];
//       var pList:List[Param] = Nil
//       if (argTypes.length > 0) for (i <- 1 to argTypes.length) {
//         // The first local variable actually represents the "this" object
//         paraNames.add(vars.get(i).name);
//         pList = Param(paraNames.get(i-1), argTypes(i-1)) :: pList
//       }
//       mList = ScalaMethod(m.name, Type.getReturnType(m.desc), pList) :: mList
//     }
//     mList
//   }
//
//
//   override def logDebug(s: => String ): Unit = {
//     println("DEBUG :: " + s)
//   }
//
//  def getTypesofClosure (obj: AnyRef): Unit = {
//
//  val cr  = getClassReader(obj.getClass)
//    val types = mutable.HashMap[String, String]()
//    cr.accept(new TypeFinderVisitor(types) , 0)
//
//
//  }
//
//
//
//  def copyFileStreamNIO(
//                         input: FileChannel,
//                         output: FileChannel,
//                         startPosition: Long,
//                         bytesToCopy: Long): Unit = {
//    val initialPos = output.position()
//    var count = 0L
//    // In case transferTo method transferred less data than we have required.
//    while (count < bytesToCopy) {
//      count += input.transferTo(count + startPosition, bytesToCopy - count, output)
//    }
//    assert(count == bytesToCopy,
//      s"request to copy $bytesToCopy bytes, but actually copied $count bytes.")
//
//    // Check the position after transferTo loop to see if it is in the right position and
//    // give user information if not.
//    // Position will not be increased to the expected length after calling transferTo in
//    // kernel version 2.6.32, this issue can be seen in
//    // https://bugs.openjdk.java.net/browse/JDK-7052359
//    // This will lead to stream corruption issue when using sort-based shuffle (SPARK-3948).
//    val finalPos = output.position()
//    val expectedPos = initialPos + bytesToCopy
//    assert(finalPos == expectedPos,
//      s"""
//         |Current position $finalPos do not equal to expected position $expectedPos
//         |after transferTo, please check your kernel version to see if it is 2.6.32,
//         |this is a kernel bug which will lead to unexpected behavior when using transferTo.
//         |You can set spark.file.transferTo = false to disable this NIO feature.
//           """.stripMargin)
//  }
//  def tryWithSafeFinally[T](block: => T)(finallyBlock: => Unit): T = {
//    var originalThrowable: Throwable = null
//    try {
//      block
//    } catch {
//      case t: Throwable =>
//        // Purposefully not using NonFatal, because even fatal exceptions
//        // we don't want to have our finallyBlock suppress
//        originalThrowable = t
//        throw originalThrowable
//    } finally {
//      try {
//        finallyBlock
//      } catch {
//        case t: Throwable if (originalThrowable != null && originalThrowable != t) =>
//          originalThrowable.addSuppressed(t)
//          logWarning(s"Suppressing exception in finally: ${t.getMessage}", t)
//          throw originalThrowable
//      }
//    }
//  }
//
//  def copyStream(
//                  in: InputStream,
//                  out: OutputStream,
//                  closeStreams: Boolean = false,
//                  transferToEnabled: Boolean = false): Long = {
//    tryWithSafeFinally {
//      if (in.isInstanceOf[FileInputStream] && out.isInstanceOf[FileOutputStream]
//        && transferToEnabled) {
//        // When both streams are File stream, use transferTo to improve copy performance.
//        val inChannel = in.asInstanceOf[FileInputStream].getChannel()
//        val outChannel = out.asInstanceOf[FileOutputStream].getChannel()
//        val size = inChannel.size()
//        copyFileStreamNIO(inChannel, outChannel, 0, size)
//        size
//      } else {
//        var count = 0L
//        val buf = new Array[Byte](8192)
//        var n = 0
//        while (n != -1) {
//          n = in.read(buf)
//          if (n != -1) {
//            out.write(buf, 0, n)
//            count += n
//          }
//        }
//        count
//      }
//    } {
//      if (closeStreams) {
//        try {
//          in.close()
//        } finally {
//          out.close()
//        }
//      }
//    }
//  }
//  // Get an ASM class reader for a given class from the JAR that loaded it
//   def getClassReader(cls: Class[_]): ClassReader = {
//    // Copy data over, before delegating to ClassReader - else we can run out of open file handles.
//    val className = cls.getName.replaceFirst("^.*\\.", "") + ".class"
//    val resourceStream = cls.getResourceAsStream(className)
//    // todo: Fixme - continuing with earlier behavior ...
//    if (resourceStream == null) return new ClassReader(resourceStream)
//
//    val baos = new ByteArrayOutputStream(128)
//    copyStream(resourceStream, baos, true)
//    new ClassReader(new ByteArrayInputStream(baos.toByteArray))
//  }
//
//  // Check whether a class represents a Scala closure
//  private def isClosure(cls: Class[_]): Boolean = {
//    cls.getName.contains("$anonfun$")
//  }
//
//  // Get a list of the outer objects and their classes of a given closure object, obj;
//  // the outer objects are defined as any closures that obj is nested within, plus
//  // possibly the class that the outermost closure is in, if any. We stop searching
//  // for outer objects beyond that because cloning the user's object is probably
//  // not a good idea (whereas we can clone closure objects just fine since we
//  // understand how all their fields are used).
//  private def getOuterClassesAndObjects(obj: AnyRef): (List[Class[_]], List[AnyRef]) = {
//    for (f <- obj.getClass.getDeclaredFields if f.getName == "$outer") {
//      f.setAccessible(true)
//      val outer = f.get(obj)
//      // The outer pointer may be null if we have cleaned this closure before
//      if (outer != null) {
//        if (isClosure(f.getType)) {
//          val recurRet = getOuterClassesAndObjects(outer)
//          return (f.getType :: recurRet._1, outer :: recurRet._2)
//        } else {
//          return (f.getType :: Nil, outer :: Nil) // Stop at the first $outer that is not a closure
//        }
//      }
//    }
//    (Nil, Nil)
//  }
//  /**
//    * Return a list of classes that represent closures enclosed in the given closure object.
//    */
//  private def getInnerClosureClasses(obj: AnyRef): List[Class[_]] = {
//    val seen = Set[Class[_]](obj.getClass)
//    val stack = Stack[Class[_]](obj.getClass)
//    while (!stack.isEmpty) {
//      val cr = getClassReader(stack.pop())
//      val set = Set.empty[Class[_]]
//      cr.accept(new InnerClosureFinder(set), 0)
//      for (cls <- set -- seen) {
//        seen += cls
//        stack.push(cls)
//      }
//    }
//    (seen - obj.getClass).toList
//  }
//
//  /**
//    * Clean the given closure in place.
//    *
//    * More specifically, this renders the given closure serializable as long as it does not
//    * explicitly reference unserializable objects.
//    *
//    * @param closure the closure to clean
//    * @param checkSerializable whether to verify that the closure is serializable after cleaning
//    * @param cleanTransitively whether to clean enclosing closures transitively
//    */
//  def clean(
//             closure: AnyRef,
//             checkSerializable: Boolean = true,
//             cleanTransitively: Boolean = true): Unit = {
//    clean(closure, checkSerializable, cleanTransitively, Map.empty)
//  }
//
//  /**
//    * Helper method to clean the given closure in place.
//    *
//    * The mechanism is to traverse the hierarchy of enclosing closures and null out any
//    * references along the way that are not actually used by the starting closure, but are
//    * nevertheless included in the compiled anonymous classes. Note that it is unsafe to
//    * simply mutate the enclosing closures in place, as other code paths may depend on them.
//    * Instead, we clone each enclosing closure and set the parent pointers accordingly.
//    *
//    * By default, closures are cleaned transitively. This means we detect whether enclosing
//    * objects are actually referenced by the starting one, either directly or transitively,
//    * and, if not, sever these closures from the hierarchy. In other words, in addition to
//    * nulling out unused field references, we also null out any parent pointers that refer
//    * to enclosing objects not actually needed by the starting closure. We determine
//    * transitivity by tracing through the tree of all methods ultimately invoked by the
//    * inner closure and record all the fields referenced in the process.
//    *
//    * For instance, transitive cleaning is necessary in the following scenario:
//    *
//    *   class SomethingNotSerializable {
//    *     def someValue = 1
//    *     def scope(name: String)(body: => Unit) = body
//    *     def someMethod(): Unit = scope("one") {
//    *       def x = someValue
//    *       def y = 2
//    *       scope("two") { println(y + 1) }
//    *     }
//    *   }
//    *
//    * In this example, scope "two" is not serializable because it references scope "one", which
//    * references SomethingNotSerializable. Note that, however, the body of scope "two" does not
//    * actually depend on SomethingNotSerializable. This means we can safely null out the parent
//    * pointer of a cloned scope "one" and set it the parent of scope "two", such that scope "two"
//    * no longer references SomethingNotSerializable transitively.
//    *
//    * @param func the starting closure to clean
//    * @param checkSerializable whether to verify that the closure is serializable after cleaning
//    * @param cleanTransitively whether to clean enclosing closures transitively
//    * @param accessedFields a map from a class to a set of its fields that are accessed by
//    *                       the starting closure
//    */
//  private def clean(
//                     func: AnyRef,
//                     checkSerializable: Boolean,
//                     cleanTransitively: Boolean,
//                     accessedFields: Map[Class[_], Set[String]]): Unit = {
//
//    if (!isClosure(func.getClass)) {
//      logWarning("Expected a closure; got " + func.getClass.getName)
//      return
//    }
//
//    // TODO: clean all inner closures first. This requires us to find the inner objects.
//    // TODO: cache outerClasses / innerClasses / accessedFields
//
//    if (func == null) {
//      return
//    }
//
//    logDebug(s"+++ Cleaning closure $func (${func.getClass.getName}) +++")
//
//    // A list of classes that represents closures enclosed in the given one
//    val innerClasses = getInnerClosureClasses(func)
//
//    // A list of enclosing objects and their respective classes, from innermost to outermost
//    // An outer object at a given index is of type outer class at the same index
//    val (outerClasses, outerObjects) = getOuterClassesAndObjects(func)
//
//    // For logging purposes only
//    val declaredFields = func.getClass.getDeclaredFields
//    val declaredMethods = func.getClass.getDeclaredMethods
//
//    if (true) {
//      logDebug(" + declared fields: " + declaredFields.size)
//      declaredFields.foreach { f => logDebug("     " + f) }
//      logDebug(" + declared methods: " + declaredMethods.size)
//      declaredMethods.foreach { m => logDebug("     " + m) }
//      logDebug(" + inner classes: " + innerClasses.size)
//      innerClasses.foreach { c => logDebug("     " + c.getName) }
//      logDebug(" + outer classes: " + outerClasses.size)
//      outerClasses.foreach { c => logDebug("     " + c.getName) }
//      logDebug(" + outer objects: " + outerObjects.size)
//      outerObjects.foreach { o => logDebug("     " + o) }
//    }
//
//    // Fail fast if we detect return statements in closures
//    getClassReader(func.getClass).accept(new ReturnStatementFinder(), 0)
//
//    // If accessed fields is not populated yet, we assume that
//    // the closure we are trying to clean is the starting one
//    if (accessedFields.isEmpty) {
//      logDebug(s" + populating accessed fields because this is the starting closure")
//      // Initialize accessed fields with the outer classes first
//      // This step is needed to associate the fields to the correct classes later
//      for (cls <- outerClasses) {
//        accessedFields(cls) = Set.empty[String]
//      }
//      // Populate accessed fields by visiting all fields and methods accessed by this and
//      // all of its inner closures. If transitive cleaning is enabled, this may recursively
//      // visits methods that belong to other classes in search of transitively referenced fields.
//      for (cls <- func.getClass :: innerClasses) {
//        getClassReader(cls).accept(new FieldAccessFinder(accessedFields, cleanTransitively), 0)
//      }
//    }
//
//    logDebug(s" + fields accessed by starting closure: " + accessedFields.size)
//    accessedFields.foreach { f => logDebug("     " + f) }
//
//    // List of outer (class, object) pairs, ordered from outermost to innermost
//    // Note that all outer objects but the outermost one (first one in this list) must be closures
//    var outerPairs: List[(Class[_], AnyRef)] = (outerClasses zip outerObjects).reverse
//    var parent: AnyRef = null
//    if (outerPairs.size > 0) {
//      val (outermostClass, outermostObject) = outerPairs.head
//      if (isClosure(outermostClass)) {
//        logDebug(s" + outermost object is a closure, so we clone it: ${outerPairs.head}")
//      } else if (outermostClass.getName.startsWith("$line")) {
//        // SPARK-14558: if the outermost object is a REPL line object, we should clone and clean it
//        // as it may carray a lot of unnecessary information, e.g. hadoop conf, spark conf, etc.
//        logDebug(s" + outermost object is a REPL line object, so we clone it: ${outerPairs.head}")
//      } else {
//        // The closure is ultimately nested inside a class; keep the object of that
//        // class without cloning it since we don't want to clone the user's objects.
//        // Note that we still need to keep around the outermost object itself because
//        // we need it to clone its child closure later (see below).
//        logDebug(" + outermost object is not a closure or REPL line object, so do not clone it: " +
//          outerPairs.head)
//        parent = outermostObject // e.g. SparkContext
//        outerPairs = outerPairs.tail
//      }
//    } else {
//      logDebug(" + there are no enclosing objects!")
//    }
//
//    // Clone the closure objects themselves, nulling out any fields that are not
//    // used in the closure we're working on or any of its inner closures.
//    for ((cls, obj) <- outerPairs) {
//      logDebug(s" + cloning the object $obj of class ${cls.getName}")
//      // We null out these unused references by cloning each object and then filling in all
//      // required fields from the original object. We need the parent here because the Java
//      // language specification requires the first constructor parameter of any closure to be
//      // its enclosing object.
//      val clone = instantiateClass(cls, parent)
//      for (fieldName <- accessedFields(cls)) {
//        val field = cls.getDeclaredField(fieldName)
//        field.setAccessible(true)
//        val value = field.get(obj)
//        field.set(clone, value)
//      }
//      // If transitive cleaning is enabled, we recursively clean any enclosing closure using
//      // the already populated accessed fields map of the starting closure
//      if (cleanTransitively && isClosure(clone.getClass)) {
//        logDebug(s" + cleaning cloned closure $clone recursively (${cls.getName})")
//        // No need to check serializable here for the outer closures because we're
//        // only interested in the serializability of the starting closure
//        clean(clone, checkSerializable = false, cleanTransitively, accessedFields)
//      }
//      parent = clone
//    }
//
//    // Update the parent pointer ($outer) of this closure
//    if (parent != null) {
//      val field = func.getClass.getDeclaredField("$outer")
//      field.setAccessible(true)
//      // If the starting closure doesn't actually need our enclosing object, then just null it out
//      if (accessedFields.contains(func.getClass) &&
//        !accessedFields(func.getClass).contains("$outer")) {
//        logDebug(s" + the starting closure doesn't actually need $parent, so we null it out")
//        field.set(func, null)
//      } else {
//        // Update this closure's parent pointer to point to our enclosing object,
//        // which could either be a cloned closure or the original user object
//        field.set(func, parent)
//      }
//    }
//
//    logDebug(s" +++ closure $func (${func.getClass.getName}) is now cleaned +++")
//
//    if (checkSerializable) {
////      ensureSerializable(func)
//    }
//  }
//
//  private def ensureSerializable(func: AnyRef) {
//    try {
//      if (SparkEnv.get != null) {
//     //   SparkEnv.get.closureSerializer.newInstance().serialize(func)
//      }
//    } catch {
//      case ex: Exception => throw new SparkException("Task not serializable", ex)
//    }
//  }
//
//  private def instantiateClass(
//                                cls: Class[_],
//                                enclosingObject: AnyRef): AnyRef = {
//    // Use reflection to instantiate object without calling constructor
//    val rf = sun.reflect.ReflectionFactory.getReflectionFactory()
//    val parentCtor = classOf[java.lang.Object].getDeclaredConstructor()
//    val newCtor = rf.newConstructorForSerialization(cls, parentCtor)
//    val obj = newCtor.newInstance().asInstanceOf[AnyRef]
//    if (enclosingObject != null) {
//      val field = cls.getDeclaredField("$outer")
//      field.setAccessible(true)
//      field.set(obj, enclosingObject)
//    }
//    obj
//  }
//
// }
//
// class ReturnStatementInClosureException
//  extends SparkException("Return statements aren't allowed in Spark closures")
//
// class ReturnStatementFinder extends ClassVisitor(ASM5) {
//  override def visitMethod(access: Int, name: String, desc: String,
//                           sig: String, exceptions: Array[String]): MethodVisitor = {
//    if (name.contains("apply")) {
//      new MethodVisitor(ASM5) {
//        override def visitTypeInsn(op: Int, tp: String) {
//          if (op == NEW && tp.contains("scala/runtime/NonLocalReturnControl")) {
//            throw new ReturnStatementInClosureException
//          }
//        }
//      }
//    } else {
//      new MethodVisitor(ASM5) {}
//    }
//  }
//}
//
///** Helper class to identify a method. */
//case class MethodIdentifier[T](cls: Class[T], name: String, desc: String)
//
///**
//  * Find the fields accessed by a given class.
//  *
//  * The resulting fields are stored in the mutable map passed in through the constructor.
//  * This map is assumed to have its keys already populated with the classes of interest.
//  *
//  * @param fields the mutable map that stores the fields to return
//  * @param findTransitively if true, find fields indirectly referenced through method calls
//  * @param specificMethod if not empty, visit only this specific method
//  * @param visitedMethods a set of visited methods to avoid cycles
//  */
//class FieldAccessFinder(
//                                       fields: Map[Class[_], Set[String]],
//                                       findTransitively: Boolean,
//                                       specificMethod: Option[MethodIdentifier[_]] = None,
//                                       visitedMethods: Set[MethodIdentifier[_]] = Set.empty)
//  extends ClassVisitor(ASM5) {
//
//  override def visitMethod(
//                            access: Int,
//                            name: String,
//                            desc: String,
//                            sig: String,
//                            exceptions: Array[String]): MethodVisitor = {
//
//    // If we are told to visit only a certain method and this is not the one, ignore it
//    if (specificMethod.isDefined &&
//      (specificMethod.get.name != name || specificMethod.get.desc != desc)) {
//      return null
//    }
//
//    new MethodVisitor(ASM5) {
//      override def visitFieldInsn(op: Int, owner: String, name: String, desc: String) {
//        if (op == GETFIELD) {
//          for (cl <- fields.keys if cl.getName == owner.replace('/', '.')) {
//            fields(cl) += name
//          }
//        }
//      }
//
//      override def visitMethodInsn(
//                                    op: Int, owner: String, name: String, desc: String, itf: Boolean) {
//        for (cl <- fields.keys if cl.getName == owner.replace('/', '.')) {
//          // Check for calls a getter method for a variable in an interpreter wrapper object.
//          // This means that the corresponding field will be accessed, so we should save it.
//          if (op == INVOKEVIRTUAL && owner.endsWith("$iwC") && !name.endsWith("$outer")) {
//            fields(cl) += name
//          }
//          // Optionally visit other methods to find fields that are transitively referenced
//          if (findTransitively) {
//            val m = MethodIdentifier(cl, name, desc)
//            if (!visitedMethods.contains(m)) {
//              // Keep track of visited methods to avoid potential infinite cycles
//              visitedMethods += m
//           //  ClosureCleaner.getClassReader(cl).accept(
//             //   new FieldAccessFinder(fields, findTransitively, Some(m), visitedMethods), 0)
//            }
//          }
//        }
//      }
//    }
//  }
//}
//
//private class InnerClosureFinder(output: Set[Class[_]]) extends ClassVisitor(ASM5) {
//  var myName: String = null
//
//  // TODO: Recursively find inner closures that we indirectly reference, e.g.
//  //   val closure1 = () = { () => 1 }
//  //   val closure2 = () => { (1 to 5).map(closure1) }
//  // The second closure technically has two inner closures, but this finder only finds one
//
//  override def visit(version: Int, access: Int, name: String, sig: String,
//                     superName: String, interfaces: Array[String]) {
//    myName = name
//  }
//
//  override def visitMethod(access: Int, name: String, desc: String,
//                           sig: String, exceptions: Array[String]): MethodVisitor = {
//    new MethodVisitor(ASM5) {
//      override def visitMethodInsn(
//                                    op: Int, owner: String, name: String, desc: String, itf: Boolean) {
//        val argTypes = Type.getArgumentTypes(desc)
//        if (op == INVOKESPECIAL && name == "<init>" && argTypes.length > 0
//          && argTypes(0).toString.startsWith("L") // is it an object?
//          && argTypes(0).getInternalName == myName) {
//          // scalastyle:off classforname
//          output += Class.forName(
//            owner.replace('/', '.'),
//            false,
//            Thread.currentThread.getContextClassLoader)
//          // scalastyle:on classforname
//        }
//      }
//    }
//  }
//}