import java.io.File
import javax.security.auth.login.Configuration

import scala.StringBuilder
import scala.collection.mutable
import scala.reflect.runtime.universe._
import scala.tools.reflect.{ToolBox, ToolBoxError}

class Extractor {

  val tb = runtimeMirror(getClass.getClassLoader).mkToolBox()

  import tb._
  import u._

  def modifyOperator(t: Tree, conf: Configuration, op: String, cl: Transformer): Select = t match {
    case b@Select(t1, t2) =>
      treeCopy.Select(b, t1, newTermName(conf.getMutation(op, "+")))
    case _ => null
  }

  def dataFlowOperationCall(name: String): Boolean = {
    Configuration.dataflowOperations.contains(name)
  }

  def checkAndenrollinMap(code: Tree , name:String): Unit ={


  }

  var operatorUDFmap : mutable.HashMap[(String , Int) , String] = new mutable.HashMap[(String , Int) , String]()
  var currentDataflowOperationCount = 0;

  def parseScalaCode(content: String, conf: Configuration): (Tree, Boolean) = {
    var isMutated = true
    try {
      val tree = tb.parse(content)
      var functiontag = !conf.getSparkConf()
      val newTree = new Transformer {
        override def transform(tree: Tree): Tree = {
          tree match {
            case a@Apply(fun, arg) =>
              fun match {
                case i @ Ident(name) =>
                  if (dataFlowOperationCall(name.toString)) {
                    for (ar <- arg) {
                      ar match {
                        case f@Function(l, tr) =>
                          println("******************\n\n" + showCode(f))
                          operatorUDFmap((name.toString , currentDataflowOperationCount)) = showCode(f)
                          currentDataflowOperationCount = currentDataflowOperationCount + 1
                        case t =>
                      }
                    }
                  }
                case Select(q, n) =>
                n match {
                  case TermName(s) =>
                    if (dataFlowOperationCall(s.toString)) {
                      for (ar <- arg) {
                        ar match {
                          case f@Function(l, tr) =>
                            println("******************\n\n" + showCode(f))
                            operatorUDFmap((s.toString , currentDataflowOperationCount)) = showCode(f)
                            currentDataflowOperationCount = currentDataflowOperationCount + 1
                          case t =>
                        }
                      }
                    }
                  case t =>
                }

                case t =>
              }
              super.transform(a)
            case t =>
              super.transform(t)
          }
        }
      }.transform(tree)
      // if(isMutated)
      //     println(showRaw(newTree))
      (newTree, isMutated)
    } catch {
      case ex: Exception =>
        ex.printStackTrace()
        null
    }
  }


 def  saveUDFsToFile(filepath: String, path: File) = {
   val pack = packageMap.getOrElse(path.getAbsolutePath, "")
   var c = new StringBuilder("")
   for((k,v)  <- operatorUDFmap){
     c.append(
       k._1 + k._2 + ":\n" + v+ "\n"
     )
   }
   val writer = new java.io.PrintWriter(filepath)
   try
     writer.write(c.mkString)
   finally writer.close()
 }



  def saveToFile(filepath: String, path: File, code: Tree) = {
    val pack = packageMap.getOrElse(path.getAbsolutePath, "")
    var c = showCode(code).trim()

    if (c(0) == '{' && c(c.length - 1) == '}') {
      c = c.substring(1)
      c = c.substring(0, c.length - 1).trim
    }
    if (c.endsWith("()")) {
      c = c.substring(0, c.length - 2)
    }
    val writer = new java.io.PrintWriter(filepath)
    try
      writer.write(pack + "\n" + c)
    finally writer.close()
  }

  def mutate(fileName: String, conf: Configuration): List[Tree] = {
    val source = scala.io.Source.fromFile(fileName)
    val lines = try {
      var str = ""
      for (l <- source.getLines()) {
        if (l.startsWith("package")) {
          packageMap += (fileName -> l)
        } else
          str += l + "\n"
      }
      str
    } finally {
      source.close()
    }

    var newTreeList: List[Tree] = List()
      val temp = parseScalaCode(lines, conf)
      if (temp._2) {
        newTreeList ::= temp._1
      }

    newTreeList
  }

  def getRecursiveListOfFiles(dir: File): Array[File] = {
    val these = dir.listFiles
    these.filter(p => p.getName.contains(".scala")) ++ these.filter(_.isDirectory).flatMap(getRecursiveListOfFiles)
  }

  var packageMap: Map[String, String] = Map[String, String]()


  def runOneFile(conf: Configuration, scalafile: String, outputfile: String): Unit = {
    val start = java.lang.System.currentTimeMillis()
    try {
      val sf = new File(scalafile)
      val mutatedList = this.mutate(sf.getAbsolutePath, conf)
      val dstFilePath = outputfile
      saveUDFsToFile(dstFilePath, sf)
      println(s"""Extraction passed on  $scalafile  """)
    } catch {
      case e: Exception => {
        e.printStackTrace()
        println(s"""Extraction failed on  $scalafile . Skipping.... """)
      }
      case _ => println(s"""Extraction failed on  $scalafile . Skipping.... """)

    }

  }

  def run(conf: Configuration, inputdir: String, pathToSrc: String, outputDir: String): Unit = {
    val start = java.lang.System.currentTimeMillis()
    println(conf.targetOp)
    println(conf.mutationMapping)
    val targetFiles = inputdir + pathToSrc
    val dir = new File(outputDir)
    if (!dir.exists()) {
      dir.mkdir()
    }

    for (scalafile <- getRecursiveListOfFiles(new File(targetFiles))) {
      val subDirIndex = scalafile.toString.indexOf(pathToSrc) + pathToSrc.length
      val filename = scalafile.getName
      try {
        //println(s"""Starting Mutation on  $filename  """)
        var count = 0
        val mutatedList = this.mutate(scalafile.getAbsolutePath, conf)
        for (mutated <- mutatedList) {
          val mutantDir = outputDir + count.toString()
          // FileUtils.copyDirectory(new File(inputdir), new File(mutantDir))
          val dstFilePath = mutantDir + scalafile.toString.substring(subDirIndex)
          saveToFile(dstFilePath, scalafile, mutated)
          count += 1
        }
        println(s"""Mutation passed on  $filename  """)
      } catch {
        case e: Exception => {
          e.printStackTrace()
          println(s"""Mutation failed on  $filename . Skipping.... """)
        }
        case _ => println(s"""Mutation failed on  $filename . Skipping.... """)

      }
    }

    val diff = java.lang.System.currentTimeMillis() - start
    println(diff)
  }

}
