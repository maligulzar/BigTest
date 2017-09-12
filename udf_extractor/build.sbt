name := "udfextractor"

version := "1.0"

scalaVersion := "2.11.8"

libraryDependencies ++= Seq(
  "org.scala-lang" % "scala-reflect" % scalaVersion.value,
  "org.scala-lang" % "scala-compiler" % scalaVersion.value,
  "org.apache.xbean" % "xbean-asm5-shaded" % "3.17",
  "org.apache.spark" %% "spark-core" % "1.6.2",
  "org.eclipse.jdt" % "org.eclipse.jdt.core" % "3.7.1",
  "org.eclipse.jdt" % "core" % "3.3.0-v_771"
)