name := "ToyExamples"

version := "1.0"

scalaVersion := "2.11.8"

mainClass in (Compile, run) := Some("AddEvenIntegers")

libraryDependencies ++= Seq(
    "org.scala-lang" % "scala-reflect" % scalaVersion.value,
    "org.apache.spark" %% "spark-core" % "1.6.2"
    )
