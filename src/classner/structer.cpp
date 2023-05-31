#include "structer.h"

void Structer::readStructs(QString filePath)
{
  this->_structs.clear();

  cout << "Reading structs...";

  QRegExp regex1(R"(struct [a-zA-Z0-9-_]+[ ][\{])");

  QFile file(filePath);
  if(!file.open(QIODevice::ReadOnly)) {
      cout << "STRUCTER ERROR: File could not be opened - " << filePath.toStdString().c_str() << endl;
  }

  bool structBody = false;
  QString curSturctName = nullptr;
  QTextStream in(&file);
  while(!in.atEnd()) {
      QString line = in.readLine().remove(QRegExp("([\n]+)$"));
      if (line.startsWith("struct ") && line.endsWith("{")) {
          if((regex1.indexIn(line, 0)) >= 0) {
              //cap = regex1.cap(1).trimmed();
              line = line.trimmed();
              line = line.replace("struct s", "struct STRUCT_");
              curSturctName = line.split(' ')[1];
              this->_structs[curSturctName] = QStringList() << line; // probably correct function name, without return type
              structBody = true;
          }
      } else if (structBody) {
          this->_structs[curSturctName].append(line);
          if (line == QString("};"))
            structBody = false;
      }
  }
  file.close();

  cout << "DONE" << endl;
}
