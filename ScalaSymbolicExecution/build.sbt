name := "Scala Symbolic Execution"

version := "1.0"

scalaVersion := "2.10.6"

libraryDependencies ++= Seq(
    "org.scala-lang" % "scala-reflect" % scalaVersion.value, 
    "com.github.scala-incubator.io" %% "scala-io-file" % "0.4.2"
    )