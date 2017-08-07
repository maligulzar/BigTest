name := "Scala Symbolic Execution"

version := "1.0"

scalaVersion := "2.10.6"

libraryDependencies ++= Seq(
    "org.scala-lang" % "scala-reflect" % scalaVersion.value, 
    "org.apache.spark" %% "spark-core" % "1.6.2",
    "com.github.scala-incubator.io" %% "scala-io-file" % "0.4.2",
    "org.scalatest" %% "scalatest" % "3.0.1" % "test"
    )