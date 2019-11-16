# SURELOG ERROR FORMATTING

def SLformatMsg (severity, category, messageId, location, text):
    chunks = []
    chunks.append("[")
    chunks.append(severity)
    chunks.append(":")
    chunks.append(category)
    chunks.append(messageId)
    chunks.append("] ")
    chunks.append(location)
    chunks.append(text)
    chunks.append("\n\n")
    result = ''.join(chunks)
    return result
