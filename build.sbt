// javaOptions in ThisBuild ++= Seq("-Xss4m", "-Xmx3g")// Seq("-Xmx1g")

fork in run := true

javaOptions in run ++=
  Seq("-Xms256M", "-Xmx2G", "-Xss512M")

// val buildSettings = Defaults.defaultSettings ++ Seq(
//   javaOptions += "-Xmx4G",
//   javaOptions += "-Xss256M"
// )
