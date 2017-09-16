name := "udfextractor"

version := "1.0"

scalaVersion := "2.11.8"

mainClass in assembly := Some("udfExtractor.Runner")

libraryDependencies ++= Seq(
  "org.scala-lang" % "scala-reflect" % scalaVersion.value,
  "org.scala-lang" % "scala-compiler" % scalaVersion.value,
  "org.apache.xbean" % "xbean-asm5-shaded" % "3.17"
  // "org.apache.spark" %% "spark-core" % "1.6.2"
)

libraryDependencies ++= Seq(
    ("org.apache.spark" %% "spark-core" % "1.6.2" % "provided").
    exclude("org.mortbay.jetty", "servlet-api").
    exclude("commons-beanutils", "commons-beanutils-core").
    exclude("commons-collections", "commons-collections").
    exclude("commons-logging", "commons-logging").
    exclude("com.esotericsoftware.minlog", "minlog")
)

assemblyMergeStrategy in assembly := {
    case PathList("META-INF", xs @ _*) => MergeStrategy.discard
    case PathList(ps @_*) if ps.last endsWith ".api_description" => MergeStrategy.discard
    case PathList(ps @_*) if ps.last endsWith ".options" => MergeStrategy.discard
    case PathList(ps @_*) if ps.last endsWith "plugin.properties" => MergeStrategy.discard
    case PathList(ps @_*) if ps.last endsWith "plugin.xml" => MergeStrategy.discard
    case x => 
        val oldStrategy = (assemblyMergeStrategy in assembly).value
        oldStrategy(x)
}