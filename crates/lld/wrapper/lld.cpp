#include <lld/Common/Driver.h>

#include <cstdlib>
#include <cstring>
#include <iostream>
#include <mutex>
#include <string>
#include <vector>

LLD_HAS_DRIVER(coff)
LLD_HAS_DRIVER(mingw)
LLD_HAS_DRIVER(elf)
LLD_HAS_DRIVER(macho)
LLD_HAS_DRIVER(wasm)

using namespace llvm;

const char *alloc_str(const std::string &str) {
    size_t size = str.length();
    if (size > 0) {
        char *strPtr = reinterpret_cast<char *>(malloc(size + 1));
        memcpy(strPtr, str.c_str(), size + 1);
        return strPtr;
    }
    return nullptr;
}

// LLD seems not to be thread safe
std::mutex _mutex;

extern "C" {
    struct LLDInvokeResult {
        bool success;
        const char *messages;
    };

    void link_free_result(LLDInvokeResult *result) {
        if (result->messages) {
            free(reinterpret_cast<void *>(const_cast<char *>(result->messages)));
        }
    }

    LLDInvokeResult lld_link(const char *flavor, int argc, const char *const *argv) {
        LLDInvokeResult result{};

        std::string outputString, errorString;
        llvm::raw_string_ostream outputStream(outputString);
        llvm::raw_string_ostream errorStream(errorString);
        std::unique_lock<std::mutex> lock(_mutex);
        
        std::vector<const char *> args;
        args.reserve(static_cast<size_t>(argc) + 3);
        args.push_back("lld");
        args.push_back("-flavor");

        std::string flavorStr = std::string(flavor);
        std::string flavorArg = std::string();
        if (flavorStr == "coff" || flavorStr == "windows") {
            flavorArg = "link";
        }
        else if (flavorStr == "mingw" ||
                 flavorStr == "elf" ||
                 flavorStr == "linux" ||
                 flavorStr == "unix") {
            flavorArg = "gnu";
        }
        else if (flavorStr == "mach-o" ||
                 flavorStr == "macho" ||
                 flavorStr == "darwin" ||
                 flavorStr == "darwinnew" ||
                 flavorStr == "ios" ||
                 flavorStr == "tvos" ||
                 flavorStr == "macos" ||
                 flavorStr == "macosx") {
            flavorArg = "darwin";
        }
        else if (flavorStr == "wasm" ||
                 flavorStr == "wasi" ||
                 flavorStr == "wasm32" ||
                 flavorStr == "wasm32-wasi" ||
                 flavorStr == "wasm32-unknown-wasi" ||
                 flavorStr == "wasm32-wasip1" ||
                 flavorStr == "wasm32-wasip1-threads" ||
                 flavorStr == "wasm32-wasip2") {
            flavorArg = "wasm";
        } else {
            errorStream << "Unknown flavor: " << flavor << "\n";
            std::string resultMessage = errorStream.str();
            result.success = false;
            result.messages = alloc_str(resultMessage);
            return result;
        }

        args.push_back(flavorArg.c_str());
        for (int i = 0; i < argc; ++i) {
            args.push_back(argv[i]);
        }
        
        lld::Result lldResult = lld::lldMain(args, outputStream, errorStream, LLD_ALL_DRIVERS);
        result.success = lldResult.retCode == 0;

        std::string resultMessage = errorStream.str() + outputStream.str();
        result.messages = alloc_str(resultMessage);
        return result;
    }
}
